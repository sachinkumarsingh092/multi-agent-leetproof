"""
Stage 5: Verification

This stage performs proof orchestration and final verification for the Velvet program.
It uses recursive decomposition to prove goals and then runs final verification.

The workflow is:
1. Proof Orchestration - Orchestrates proving goals via recursive decomposition
2. Final Verification - Runs lake build to verify the complete proof

NOTE: This module is deprecated. Use pipeline.run_verification() instead,
which uses the container pattern for proper DBOS integration.
"""

from langgraph.graph import StateGraph, START, END
from agents.agent_state import VelvetAgentState
from workflow_helpers import final_verification
from logging_config import get_logger

logger = get_logger(__name__)


# Node names
PROOF_ORCHESTRATION = "proof_orchestration"
FINAL_VERIFICATION = "final_verification"


def create_verification_workflow():
    """
    Create the verification workflow.

    Returns a compiled StateGraph that:
    1. Orchestrates proof generation via recursive decomposition
    2. Performs final verification with lake build

    NOTE: Prefer using pipeline.run_verification() which uses the container.
    """
    from container import get_container

    workflow = StateGraph(VelvetAgentState)

    container = get_container()
    workflow.add_node(
        PROOF_ORCHESTRATION, container.orchestrator.as_node()
    )
    workflow.add_node(FINAL_VERIFICATION, final_verification)

    # Define edges - simple linear flow
    workflow.add_edge(START, PROOF_ORCHESTRATION)
    workflow.add_edge(PROOF_ORCHESTRATION, FINAL_VERIFICATION)
    workflow.add_edge(FINAL_VERIFICATION, END)

    return workflow.compile()
