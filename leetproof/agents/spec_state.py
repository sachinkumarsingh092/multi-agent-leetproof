from typing import TypedDict
from enum import Enum


class CoachVerdict(str, Enum):
    """Verdict from coach agent."""
    ACCEPT = "ACCEPT"
    ACCEPT_WITH_MINOR_ISSUES = "ACCEPT_WITH_MINOR_ISSUES"
    REJECT = "REJECT"
    PENDING = "PENDING"  # Initial state before judgment


class SpecAgentState(TypedDict):
    """State for the Specification Generation workflow."""
    # Input
    problem_description: str  # Natural language problem description
    problem_id: str  # Problem identifier (e.g., "mbpp_46")
    output_file: str  # Path to write the specification

    # Planning state (new)
    planning_results: str  # Results from planning phase (includes Mathlib definitions and RAG examples)

    # SpecGen state
    current_spec: str  # Current specification content
    build_log: str  # Build/typecheck output
    typechecks: bool  # Whether spec typechecks
    has_axiom: bool  # Whether axioms were detected (not allowed)
    sorry_count: int  # Number of sorry statements (should be exactly 1)
    extracted_goals_typecheck_passed: bool | None  # Whether extracted goals typecheck as sorried theorems
    specgen_attempt: int  # Current attempt number
    specgen_max_attempt: int

    # SpecCoach state
    coach_verdict: CoachVerdict  # Verdict from coach
    coach_feedback: str  # Detailed feedback from coach
    coach_score: int  # Total score from coach (0-40)

    # Best specification with minor issues (fallback)
    best_minor_issues_spec: str  # Best spec that got ACCEPT_WITH_MINOR_ISSUES
    best_minor_issues_score: int  # Score of the best minor issues spec
    best_minor_issues_typechecks: bool  # Whether that spec typechecks
    best_minor_issues_coach_verdict: CoachVerdict  # Coach verdict for that spec

    # ExampleProver state
    example_verify_file: str  # Path to example_verify.lean file
    example_verify_content: str  # Content of verification file
    proof_typechecks: bool  # Whether proofs typecheck
    proof_build_log: str  # Build log for proofs
    proof_attempt: int  # Proof attempt counter
    proven_count: int  # Number of theorems actually proven

    # ProofGuide state
    proof_guide_feedback: str  # Feedback from proof guide

    # SpecPBT state
    pbt_result: str  # Result of property-based testing (see stages/spec_pbt.py)
    pbt_detail: str  # Human-readable detail from PBT (which case failed, counter-example)

    # Attempt history (accumulated across retries)
    # Each entry: {"attempt": int, "spec": str, "typechecks": bool,
    #              "build_log": str, "coach_verdict": str, "coach_feedback": str}
    spec_history: list


class ExampleProverState(TypedDict):
    """State for the ExampleProver agent (internal loop)."""
    spec_file: str  # Path to specification file
    verify_file: str  # Path to verification file to generate
    spec_content: str  # Content of specification
    current_proof: str  # Current proof content
    build_log: str  # Build output
    typechecks: bool  # Whether proofs typecheck
    attempt: int  # Current attempt number
    proof_guide_feedback: str  # Feedback from ProofGuide
