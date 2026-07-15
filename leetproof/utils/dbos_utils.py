import re
from typing import Optional, Tuple

from logging_config import get_logger

logger = get_logger(__name__)


async def _find_failed_step(workflow_id: str, DBOS) -> int:
    """Find the step number where the workflow failed.

    Returns the function_id of the failed step, or 1 if not found.
    This allows forking from just before the failure.
    """
    try:
        steps = await DBOS.list_workflow_steps_async(workflow_id)
        if not steps:
            logger.info("No steps found, forking from step 1")
            return 1

        # Log all steps for debugging
        for step in steps:
            has_error = step.get("error") is not None
            logger.info(f"  Step {step['function_id']}: {step['function_name']} (error={has_error})")

        # Find the step with an error
        for step in steps:
            if step.get("error") is not None:
                failed_step = step["function_id"]
                logger.info(f"Found failed step: {failed_step} ({step['function_name']})")
                return failed_step

        # No error found in steps - might be in child workflow
        # Fork from the last step to re-run it
        last_step = max(s["function_id"] for s in steps)
        logger.info(f"No failed step found, forking from last step: {last_step}")
        return last_step

    except Exception as e:
        logger.warning(f"Error finding failed step: {e}, defaulting to step 1")
        return 1


async def _find_latest_workflow_id(base_session_name: str, DBOS) -> Tuple[Optional[str], int]:
    """Find the latest workflow ID for a session (original or retries).

    Returns:
        Tuple of (workflow_id, max_retry_number).
        workflow_id is None if no workflow found.
        max_retry_number is 0 if only original exists, or the highest retry number.
    """
    all_workflows = await DBOS.list_workflows_async()

    # Pattern to match retries: session_name_retry1, session_name_retry2, etc.
    pattern = re.compile(rf"^{re.escape(base_session_name)}_retry(\d+)$")

    max_retry = -1
    latest_id = None

    for wf in all_workflows:
        if wf.workflow_id == base_session_name:
            if max_retry < 0:
                latest_id = base_session_name
                max_retry = 0
        else:
            match = pattern.match(wf.workflow_id)
            if match:
                retry_num = int(match.group(1))
                if retry_num > max_retry:
                    max_retry = retry_num
                    latest_id = wf.workflow_id

    return latest_id, max(max_retry, 0)


async def run_or_resume_workflow(
    session_name: str,
    resume: bool,
    coro_fn,
    fork_from_step: Optional[int] = None,
):
    """Run a DBOS workflow, or resume/fork it intelligently.

    On fresh start: assigns session_name as the workflow ID via SetWorkflowID
    and invokes coro_fn().

    On resume:
    - Finds the latest workflow (original or _retryN)
    - SUCCESS: return cached result
    - PENDING/ENQUEUED: wait for completion (normal resume)
    - ERROR: fork from specified step with new _retryN ID

    Args:
        session_name: The workflow ID / session name.
        resume: Whether to resume an existing workflow.
        coro_fn: A zero-argument callable that returns the coroutine to run
                 (only called on fresh start).
        fork_from_step: Step to fork from on ERROR. If None (default),
                        automatically finds the failed step.
    """
    from dbos import DBOS

    if resume:
        # Find the latest workflow (original or any retry)
        latest_id, max_retry = await _find_latest_workflow_id(session_name, DBOS)

        if latest_id is None:
            logger.warning(f"No workflow found for session '{session_name}', starting fresh")
            resume = False
        else:
            workflows = await DBOS.list_workflows_async(workflow_ids=[latest_id])
            status = workflows[0].status
            logger.info(f"Latest workflow '{latest_id}' status: {status}")

            if status == "SUCCESS":
                logger.info("Workflow completed successfully, returning cached result")
                handle = await DBOS.retrieve_workflow_async(latest_id)
                return await handle.get_result()

            elif status == "ERROR":
                # Fork to retry from before the failure
                from dbos import SetWorkflowID

                # Find the step that failed and fork from there
                if fork_from_step is not None:
                    start_step = fork_from_step
                else:
                    start_step = await _find_failed_step(latest_id, DBOS)

                new_retry_num = max_retry + 1
                new_workflow_id = f"{session_name}_retry{new_retry_num}"

                logger.info(f"Workflow failed, forking from step {start_step}")
                logger.info(f"New workflow ID: {new_workflow_id}")

                with SetWorkflowID(new_workflow_id):
                    handle = await DBOS.fork_workflow_async(latest_id, start_step=start_step)

                return await handle.get_result()

            elif status in ("PENDING", "ENQUEUED"):
                logger.info(f"Workflow is {status}, waiting for completion")
                handle = await DBOS.retrieve_workflow_async(latest_id)
                return await handle.get_result()

            else:
                # CANCELLED, RETRIES_EXCEEDED, or unknown
                logger.warning(f"Workflow status is {status}, attempting retrieve")
                handle = await DBOS.retrieve_workflow_async(latest_id)
                return await handle.get_result()

    if not resume:
        logger.info("Starting new workflow")
        from dbos import SetWorkflowID
        with SetWorkflowID(session_name):
            return await coro_fn()
