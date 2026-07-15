"""
Stage 4: Invariant Generation

This stage improves loop invariants in the Velvet program.
The inferrer agent handles generation, typechecking, and judge review internally.
"""

from langgraph.graph import StateGraph, START, END
from agents.agent_state import VelvetAgentState
from logging_config import get_logger

logger = get_logger(__name__)


# Node names
IMPROVE_INVARIANTS = "improve_invariants"


def create_invariant_generate_workflow():
    """
    Create the invariant generation workflow.

    Returns a compiled StateGraph that improves loop invariants in the Velvet program.
    The inferrer agent handles typechecking and judge review internally.
    If the method has no while loops, it skips automatically.
    """
    from container import get_container

    container = get_container()
    workflow = StateGraph(VelvetAgentState)

    # Add nodes - inferrer handles everything (generate, typecheck, judge)
    workflow.add_node(
        IMPROVE_INVARIANTS,
        container.inferrer.as_node()
    )

    # Simple flow: START -> IMPROVE -> END
    workflow.add_edge(START, IMPROVE_INVARIANTS)
    workflow.add_edge(IMPROVE_INVARIANTS, END)

    return workflow.compile()
