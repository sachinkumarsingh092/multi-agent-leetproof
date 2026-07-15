"""
Stage 3: Code Generation

This stage generates a Velvet program from the specification.
The programmer agent handles generation, typechecking, and judge review internally.
"""

from langgraph.graph import StateGraph, START, END
from agents.agent_state import VelvetAgentState
from logging_config import get_logger

logger = get_logger(__name__)


# Node names
GENERATE_VELVET = "generate_velvet_program"


def create_code_generate_workflow():
    """
    Create the code generation workflow.

    Returns a compiled StateGraph that generates a Velvet program from specification.
    The programmer agent handles typechecking and judge review internally.
    """
    from container import get_container

    container = get_container()
    workflow = StateGraph(VelvetAgentState)

    # Add nodes - programmer handles everything (generate, typecheck, judge)
    workflow.add_node(
        GENERATE_VELVET,
        container.programmer.as_node()
    )

    # Simple flow: START -> GENERATE -> END
    workflow.add_edge(START, GENERATE_VELVET)
    workflow.add_edge(GENERATE_VELVET, END)

    return workflow.compile()
