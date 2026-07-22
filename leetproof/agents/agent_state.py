from typing import List, TypedDict, TYPE_CHECKING, Optional, Dict, NotRequired
from enum import Enum

if TYPE_CHECKING:
    from utils.lean_helpers import Goal
    from utils.proof_types import ProofResult
from utils.program_state import ProgramState


class AgentException(Exception):
    """Base exception for agent failures."""

    def __init__(self, agent_name: str, message: str = ""):
        self.agent_name = agent_name
        full_message = f"Agent '{agent_name}'"
        if message:
            full_message += f": {message}"
        super().__init__(full_message)


class RetryLimitExceeded(AgentException):
    """Raised when an agent exhausts its retry attempts without success."""

    def __init__(self, agent_name: str, attempts: int, reason: str = ""):
        self.attempts = attempts
        self.reason = reason
        message = f"exhausted {attempts} attempts"
        if reason:
            message += f" - {reason}"
        super().__init__(agent_name, message)


class JudgeVerdict(str, Enum):
    """Verdict from judge agent."""

    PASS = "PASS"
    FAIL = "FAIL"
    NOT_REQUIRED = "NOT_REQUIRED"
    PENDING = "PENDING"  # Initial state before judgment


class GoalStatus(str, Enum):
    """Status of a goal during processing."""

    UNPROCESSED = "UNPROCESSED"
    IN_PROGRESS = "IN_PROGRESS"
    PROVEN = "PROVEN"
    PARTIAL = "PARTIAL"  # Proof exists but contains sorry (subgoals failed)
    FAILED = "FAILED"  # Complete failure, no proof in file


class PBTStatus(str, Enum):
    """Status of Property-Based Testing attempt."""

    NOT_ATTEMPTED = "NOT_ATTEMPTED"
    ADDED_AND_PASSED = "ADDED_AND_PASSED"  # PBT added, ran successfully
    ADDED_COMPILE_FAILED = "ADDED_COMPILE_FAILED"  # PBT added but failed to compile
    NOT_ADDED = "NOT_ADDED"  # Attempted but couldn't add PBT


class GoalState(TypedDict):
    """State of a single goal from loom_solve during processing."""

    goal: "Goal"  # Goal object from utils.lean_helpers
    status: GoalStatus
    description: str  # Optional description or failure reason
    failures: List  # List of failure info from prover agent (optional)
    proof_result: Optional[
        "ProofResult"
    ]  # Full proof result with decomposition tree (optional)


class VelvetAgentState(TypedDict):
    """State for the Velvet Programmer agent."""

    specification: str
    program_state: ProgramState  # Program buffer state for syncing content
    build_log: str
    typechecks: bool
    attempt: int  # Attempts within current agent invocation
    judge_rejections: Dict[
        str, int
    ]  # Number of judge rejections per agent (keyed by agent name)
    output_file: str
    judge_verdict: JudgeVerdict  # Verdict from judge agent
    judge_reasoning: str  # Full reasoning from judge for feedback to agent
    phase_results: Dict[str, Dict]  # Results from each agent (keyed by agent name)
    judge_context: Dict[str, str]  # Additional context sections for judge
    goals: List[GoalState]  # List of goals from loom_solve
    pbt_status: PBTStatus  # Status of Property-Based Testing attempt
    continuation_ctx: Dict[str, str]  # For context injections when we want to pass certain information from one node to another
    previous_attempt_impl: NotRequired[str]  # Prior Impl section before the latest retry
    goal_extraction_grind_gen_param: NotRequired[int | None]  # Custom grind gen used to extract goals after loom_solve, if any
    formal_contract_file: NotRequired[str]  # Immutable session-scoped contract artifact
    formal_contract_sha256: NotRequired[str]  # SHA-256 of the immutable contract
