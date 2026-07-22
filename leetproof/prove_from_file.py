from __future__ import annotations

import logging
from pathlib import Path
from typing import TYPE_CHECKING

from agents.prover_v2_agent import PROVE_GOAL_V2_DEFAULT_MAX_ITERATIONS, ProverV2Agent

if TYPE_CHECKING:
    from agents.prover_agent import ProverAgent

logger = logging.getLogger(__name__)


async def prove_from_file(
    input_file: str,
    output_file: str,
    *,
    prover_v2: ProverV2Agent,
    prover: ProverAgent,
    max_depth: int = 3,
    max_iterations: int = PROVE_GOAL_V2_DEFAULT_MAX_ITERATIONS,
) -> dict:
    """Extract sorry'd goals from input_file and prove them into output_file."""
    import os

    from utils.context_utils import SectionExtractor
    from utils.lean.constants import (
        PANTOGRAPH_CORE_OPTIONS,
        PANTOGRAPH_OPTIONS,
        VELVET_AUTOMATION,
    )
    from utils.lean.parser import LeanFile
    from utils.proof_types import (
        AttemptBudgetConfig,
        AttemptBudgetConfigBundle,
        AttemptBudgetMode,
        PantographParams,
        ProvingContext,
    )
    from utils.sorry_extraction import extract_sorry_goals

    lean_file = LeanFile.from_path(input_file)
    result = extract_sorry_goals(lean_file, "Proof")

    if not result.sorry_goals:
        logger.info("No sorry'd goals found — copying input to output unchanged")
        Path(output_file).write_text(Path(input_file).read_text())
        return {"total": 0, "proved": 0, "failed": 0}

    logger.info(
        f"Found {len(result.sorry_goals)} sorry'd goal(s): "
        f"{[sg.name for sg in result.sorry_goals]}"
    )

    out_parts: list[str] = []
    for imp in result.imports:
        out_parts.append(f"import {imp}")
    if result.prologue_body:
        out_parts.append(result.prologue_body)

    preserve_sections = ["Specs"]
    for section in lean_file.sections:
        if section.name in preserve_sections:
            out_parts.append(section.full_text().strip())

    out_parts.append("section Proof\n\nend Proof")

    Path(output_file).write_text("\n\n".join(out_parts) + "\n")
    logger.info(f"Wrote initial output file: {output_file}")

    all_sections = preserve_sections + ["Proof"]
    context_sections = preserve_sections
    project_path = os.getcwd()

    attempt_budgets = AttemptBudgetConfigBundle(
        shallow=AttemptBudgetConfig(
            mode=AttemptBudgetMode.UP, base=5, slope=5, min_attempts=5, max_attempts=15,
        ),
        decomposition=AttemptBudgetConfig(
            mode=AttemptBudgetMode.DOWN, base=10, slope=2, min_attempts=5, max_attempts=10,
        ),
    )

    results: list[dict] = []
    for i, sg in enumerate(result.sorry_goals):
        goal = sg.goal
        logger.info(f"\n{'=' * 60}")
        logger.info(f"  [{i+1}/{len(result.sorry_goals)}] Proving: {goal.name}")
        logger.info(f"{'=' * 60}")

        ctx = ProvingContext(
            file_path=output_file,
            goal=goal,
            sections=all_sections,
            pantograph=PantographParams(
                key=goal.name,
                project_path=project_path,
                imports=result.imports,
                options=PANTOGRAPH_OPTIONS,
                core_options=list(PANTOGRAPH_CORE_OPTIONS),
            ),
            automation_tactics=list(VELVET_AUTOMATION),
            informal_reasoning="",
            context_extractor=SectionExtractor(context_sections),
            attempt_budgets=attempt_budgets,
            hint_sections=preserve_sections[:1],
        )

        proof_result = await prover_v2.prove(
            ctx=ctx,
            max_depth=max_depth,
            max_iterations=max_iterations,
        )

        status = "proved" if proof_result.success and not proof_result.has_sorry else (
            "partial" if proof_result.success else "failed"
        )
        logger.info(f"  Result: {status} — {goal.name}")
        if proof_result.error:
            logger.info(f"  Error: {proof_result.error[:200]}")

        results.append({
            "name": goal.name,
            "status": status,
            "has_sorry": proof_result.has_sorry,
        })

    proved = sum(1 for r in results if r["status"] == "proved")
    partial = sum(1 for r in results if r["status"] == "partial")
    failed = sum(1 for r in results if r["status"] == "failed")

    logger.info(f"\n{'=' * 60}")
    logger.info(f"  DONE: {proved} proved, {partial} partial, {failed} failed out of {len(results)}")
    logger.info(f"  Output: {output_file}")
    logger.info(f"{'=' * 60}")

    return {
        "total": len(results),
        "proved": proved,
        "partial": partial,
        "failed": failed,
        "goals": results,
    }


def main() -> None:
    """CLI entry point for prove-from-file."""
    import os
    import sys

    from args import merge_session_params, parse_args, save_session_params
    from config.constants import SESSIONS_DIR

    args = parse_args()

    project_dir = os.path.abspath(args.project)
    if not os.path.isdir(project_dir):
        print(f"Error: --project directory does not exist: {project_dir}")
        sys.exit(1)
    os.chdir(project_dir)

    session_name = args.session_name
    if not session_name:
        print("Error: --session-name is required")
        sys.exit(1)

    merge_session_params(args)

    if not args.provider:
        print("Error: --provider is required")
        sys.exit(1)
    if not args.model:
        print("Error: --model is required")
        sys.exit(1)
    if not args.input_file:
        print("Error: --input-file is required")
        sys.exit(1)
    if not args.output_file:
        print("Error: --output-file is required for prove-from-file")
        sys.exit(1)

    input_file = os.path.abspath(args.input_file)
    output_file = os.path.abspath(args.output_file)

    if input_file == output_file:
        print("Error: --input-file and --output-file must differ")
        sys.exit(1)
    if not os.path.isfile(input_file):
        print(f"Error: input file does not exist: {input_file}")
        sys.exit(1)

    session_dir = Path(SESSIONS_DIR) / session_name
    session_dir.mkdir(parents=True, exist_ok=True)
    logger.info(f"Session directory: {session_dir}")

    save_session_params(
        session_name=session_name,
        provider=args.provider,
        model=args.model,
        input_file=input_file,
        output_file=output_file,
        max_input_tokens=args.max_input_tokens,
        max_output_tokens=args.max_output_tokens,
        max_total_tokens=args.max_total_tokens,
        max_cost=args.max_cost,
        agent_context=args.agent_context,
        prover_v2_max_iterations=args.prover_v2_max_iterations,
    )
    logger.info(f"Session params saved to {session_dir / 'session_params.json'}")

    resume = getattr(args, "resume", False)

    ProverV2Agent._init_dbos_standalone(
        provider=args.provider,
        model=args.model,
        session_name=session_name,
        max_input_tokens=args.max_input_tokens,
        max_output_tokens=args.max_output_tokens,
        max_total_tokens=args.max_total_tokens,
        max_cost=args.max_cost,
        agent_context=args.agent_context,
        skip_container=True,
        resume=resume,
    )

    from agents.proof_reasoning_agent import ProofReasoningAgent
    from agents.prover_agent import ProverAgent
    from agents.retriever_agent import RetrieverAgent
    from dbos import DBOS
    from providers import LLMConfig, ReasoningLevel
    from runner import run

    config = LLMConfig(provider=args.provider, model=args.model)
    retriever = RetrieverAgent(config)
    reasoning = ProofReasoningAgent(config, reasoning_level=ReasoningLevel.MEDIUM)
    prover = ProverAgent(config, retriever=retriever, reasoning=reasoning)
    prover_v2 = ProverV2Agent(
        config,
        prover=prover,
        retriever=retriever,
        reasoning=reasoning,
        reasoning_level=ReasoningLevel.MEDIUM,
    )

    DBOS.launch()
    logger.info("DBOS launched for prove-from-file")

    async def workflow():
        return await prove_from_file(
            input_file=input_file,
            output_file=output_file,
            prover_v2=prover_v2,
            prover=prover,
            max_iterations=args.prover_v2_max_iterations or PROVE_GOAL_V2_DEFAULT_MAX_ITERATIONS,
        )

    try:
        run(workflow)
    except KeyboardInterrupt:
        sys.exit(130)
