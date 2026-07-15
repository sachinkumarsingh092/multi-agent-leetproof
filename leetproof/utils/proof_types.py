"""Proof types used by ProverAgent and its callers.

Extracted from prover_agent.py so that consumers (e.g. agent_state, tests)
can import these types without importing the full agent module.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Literal, Optional, TYPE_CHECKING

if TYPE_CHECKING:
    from utils.lean.types import Goal, LakeBuildResult
    from utils.context_utils import ContextExtractor
    from utils.lean_explore_service import LeanExploreResult


@dataclass
class FailureInfo:
    """Information about a failure during proof generation."""

    phase: str  # "shallow_solve", "decomposition", "subgoal_proof", "assembly"
    goal_name: str  # Name of the goal/theorem that failed
    depth: int  # Recursion depth where failure occurred
    error: str  # Error message
    attempted_proof: str = ""  # The proof that was attempted (if any)


@dataclass
class ProofResult:
    """Result of a proof attempt."""

    success: bool  # True if proved (possibly with sorry), False if failed
    content: str  # File content after proof attempt
    proof: str  # The theorem proof code (may contain sorry)
    lemmas: list[str] = field(default_factory=list)
    error: str = ""  # Error message if failed
    failures: list[FailureInfo] = field(default_factory=list)  # All failures encountered
    has_sorry: bool = False  # True if proof contains sorry
    filtered_goal: "Goal | None" = None  # Goal with unused params removed (if any)

    def to_dict(self) -> dict:
        """Convert to dict for DBOS serialization."""
        return {
            "success": self.success,
            "content": self.content,
            "proof": self.proof,
            "error": self.error,
            "failures": [
                {
                    "phase": f.phase,
                    "goal_name": f.goal_name,
                    "depth": f.depth,
                    "error": f.error,
                    "attempted_proof": f.attempted_proof,
                }
                for f in self.failures
            ],
            "has_sorry": self.has_sorry,
            "filtered_goal": self.filtered_goal.to_dict() if self.filtered_goal else None,
        }

    def get_failure_summary(self) -> str:
        """Get a human-readable summary of all failures."""
        if not self.failures:
            return "No failures"

        summary = []
        summary.append(f"Total failures: {len(self.failures)}")
        summary.append("")

        for i, failure in enumerate(self.failures, 1):
            summary.append(f"{i}. {failure.phase} failure at depth {failure.depth}:")
            summary.append(f"   Goal: {failure.goal_name}")
            summary.append(f"   Error: {failure.error[:200]}...")
            summary.append("")

        return "\n".join(summary)


@dataclass
class PantographParams:
    """Parameters for initializing a PantographClient."""
    key: str
    project_path: str
    imports: list[str] = field(default_factory=lambda: ["Init"])
    options: dict = field(default_factory=dict)
    core_options: list[str] = field(default_factory=list)


@dataclass
class ExistingPantographClient:
    """Use an existing PantographClient from PantographFactory by key."""

    key: str


@dataclass
class NewPantographClient:
    """Create a new ephemeral PantographClient (closed after discovery)."""

    project_path: str
    imports: list[str]
    options: dict
    core_options: list[str] = field(default_factory=list)


PantographSource = ExistingPantographClient | NewPantographClient


class AttemptBudgetMode(Enum):
    """Policy mode for how attempt budgets scale with depth."""

    UP = "up"
    DOWN = "down"


@dataclass(frozen=True)
class AttemptBudgetConfig:
    """Configuration for attempt budgets per depth."""

    mode: AttemptBudgetMode
    base: int
    slope: int
    min_attempts: int
    max_attempts: int


@dataclass(frozen=True)
class AttemptBudgetConfigBundle:
    """Attempt budget configuration for shallow and decomposition loops."""

    shallow: AttemptBudgetConfig
    decomposition: AttemptBudgetConfig


@dataclass
class ProvingContext:
    """Shared context for a single prove_goal invocation.

    File content is always read from disk via read_file() — no caching,
    no staleness. The file on disk is the single source of truth.
    """
    file_path: str
    goal: "Goal"
    sections: list[str]  # Sections to load on pantograph in order
    pantograph: PantographParams
    automation_tactics: list[str]  # Tactics to try before MCTS proof search
    informal_reasoning: str  # Must be explicit — use "" if not yet available
    context_extractor: "ContextExtractor"  # Extracts relevant context for LLM prompts
    attempt_budgets: AttemptBudgetConfigBundle
    hint_sections: list[str] = field(default_factory=list)  # Sections to analyze for proof hints
    pending_lemma_blocks: list[str] = field(default_factory=list)  # Helper lemmas available in context but not yet persisted to file
    proof_hints: Optional["ProofHints"] = None  # Pre-populated by caller or discover_hints_and_prove()

    def read_file(self) -> str:
        """Read the current file content from disk."""
        from pathlib import Path
        return Path(self.file_path).read_text()

    def get_relevant_context(self) -> str:
        """Read the file and extract relevant context for LLM prompts."""
        context = self.context_extractor.extract(self.read_file())
        lemma_blocks = [block.strip() for block in self.pending_lemma_blocks if block.strip()]
        if not lemma_blocks:
            return context

        pending = "\n\n".join(lemma_blocks)
        return f"{context}\n\n-- Pending helper lemmas\n{pending}"

    def copy_with(
        self,
        *,
        file_path: "str | None" = None,
        goal: "Goal | None" = None,
        sections: "list[str] | None" = None,
        pantograph: "PantographParams | None" = None,
        automation_tactics: "list[str] | None" = None,
        informal_reasoning: "str | None" = None,
        context_extractor: "ContextExtractor | None" = None,
        hint_sections: "list[str] | None" = None,
        attempt_budgets: "AttemptBudgetConfigBundle | None" = None,
        pending_lemma_blocks: "list[str] | None" = None,
    ) -> "ProvingContext":
        """Return a copy with selected fields overridden.

        proof_hints is always inherited — set once by prove().
        """
        return ProvingContext(
            file_path=file_path if file_path is not None else self.file_path,
            goal=goal if goal is not None else self.goal,
            sections=sections if sections is not None else self.sections,
            pantograph=pantograph if pantograph is not None else self.pantograph,
            automation_tactics=automation_tactics if automation_tactics is not None else self.automation_tactics,
            informal_reasoning=informal_reasoning if informal_reasoning is not None else self.informal_reasoning,
            context_extractor=context_extractor if context_extractor is not None else self.context_extractor,
            attempt_budgets=attempt_budgets if attempt_budgets is not None else self.attempt_budgets,
            hint_sections=hint_sections if hint_sections is not None else self.hint_sections,
            pending_lemma_blocks=pending_lemma_blocks if pending_lemma_blocks is not None else self.pending_lemma_blocks,
            proof_hints=self.proof_hints,
        )

    @property
    def temp_section(self) -> str:
        return f"Proof_{self.goal.name}"

    @property
    def goal_name(self) -> str:
        return self.goal.name

    @property
    def goal_theorem(self) -> str:
        return self.goal.as_sorried()


@dataclass
class IterationFeedback:
    """Carries feedback between retry iterations in shallow solve and decomposition loops."""
    error: Optional[str] = None
    previous_attempt: Optional[str] = None


@dataclass
class AutomationResult:
    """Result of trying automation tactics on a goal."""
    success: bool
    applied_tactic: "str | list[str]" = ""
    proof: str = ""
    build_result: "LakeBuildResult | None" = None


@dataclass
class SubgoalInfo:
    """Information about a subgoal in decomposition."""

    goal: "Goal"
    proved_statement: str = ""
    has_sorry: bool = True

    @property
    def name(self) -> str:
        """Full name like 'parent_0', 'parent_1'."""
        return self.goal.name

    @property
    def statement(self) -> str:
        """Full theorem statement with sorry."""
        return self.goal.as_sorried()


@dataclass
class DecompositionResult:
    """Result of extracting subgoals from a proof sketch."""
    subgoals: "list[SubgoalInfo]"
    assembled_sketch: str
    error: str | None = None

    @property
    def success(self) -> bool:
        return self.error is None

    @staticmethod
    def failure(error: str) -> "DecompositionResult":
        return DecompositionResult(subgoals=[], assembled_sketch="", error=error)


@dataclass
class SubgoalOutcome:
    """Result of proving a single subgoal."""
    name: str
    proof: str
    success: bool  # True = fully proven
    partial: bool  # True = proven but with sorry
    result: "ProofResult"


@dataclass
class ProofHints:
    """Hints for proof generation, discovered from project symbols and dependencies."""
    user_constants: list[str]
    user_constructors: list[str]
    ranked_symbols: list[str]                    # Just names, ranked by relevance
    discovered_lemmas: "list[LeanExploreResult]"  # Filtered lemma results
    grindable_lemmas: list[str] = field(default_factory=list)  # Names accepted by `attribute [grind]`

    def __str__(self) -> str:
        parts = [f"ProofHints(constants={len(self.user_constants)}, "
                 f"constructors={len(self.user_constructors)}, "
                 f"symbols={len(self.ranked_symbols)}, "
                 f"lemmas={len(self.discovered_lemmas)}, "
                 f"grindable={len(self.grindable_lemmas)})"]
        if self.user_constants:
            parts.append(f"  constants: {', '.join(self.user_constants)}")
        if self.user_constructors:
            parts.append(f"  constructors: {', '.join(self.user_constructors)}")
        if self.ranked_symbols:
            preview = self.ranked_symbols[:10]
            suffix = f" ... (+{len(self.ranked_symbols) - 10} more)" if len(self.ranked_symbols) > 10 else ""
            parts.append(f"  symbols: {', '.join(preview)}{suffix}")
        if self.discovered_lemmas:
            preview = self.discovered_lemmas[:5]
            suffix = f" ... (+{len(self.discovered_lemmas) - 5} more)" if len(self.discovered_lemmas) > 5 else ""
            parts.append(f"  lemmas: {', '.join(l.name for l in preview)}{suffix}")
        if self.grindable_lemmas:
            preview = self.grindable_lemmas[:8]
            suffix = f" ... (+{len(self.grindable_lemmas) - 8} more)" if len(self.grindable_lemmas) > 8 else ""
            parts.append(f"  grindable: {', '.join(preview)}{suffix}")
        return "\n".join(parts)

    __repr__ = __str__

    def format_hints(self) -> str:
        """Format as a string suitable for LLM prompts."""
        parts = []
        if self.user_constants:
            parts.append("# User Definitions\n" + "\n".join(f"- {c}" for c in self.user_constants))
        if self.discovered_lemmas:
            parts.append("# Hints From User Symbols\n" + "\n".join(
                f"- {l.name}: {l.statement}" for l in self.discovered_lemmas
            ))
        return "\n\n".join(parts)

    def format_lemmas(self) -> str:
        """Format only discovered lemmas — for contexts where file definitions are already available."""
        if not self.discovered_lemmas:
            return ""
        return "# Discovered Lemmas\n" + "\n".join(
            f"- {l.name}: {l.statement}" for l in self.discovered_lemmas
        )


# ── prove_goalv2 types ──────────────────────────────────────────────


@dataclass
class ProofSubmission:
    """Result of a check_theorem tool call."""

    proof: str
    build_result: LakeBuildResult

    @property
    def typechecks(self) -> bool:
        return self.build_result.typechecks


@dataclass
class SketchSubmission:
    """Result of a decompose_goal tool call."""

    sketch: str
    build_result: LakeBuildResult
    subgoals: list[SubgoalInfo] = field(default_factory=list)
    assembled_sketch: str = ""
    error: str = ""  # Extraction or correctness failure

    @property
    def typechecks(self) -> bool:
        return self.build_result.typechecks

    @property
    def has_valid_subgoals(self) -> bool:
        return self.typechecks and len(self.subgoals) > 0 and not self.error


@dataclass
class LemmaRegistration:
    """A helper declaration registered into the proving context."""

    name: str
    proof: str
    active: bool = False  # True if typechecked and loaded into pantograph
    error: str = ""  # Error message if typecheck failed


@dataclass
class DonePayload:
    """Payload for the done() tool call."""

    outcome: Literal["proved", "decompose", "stuck"]
    note: str = ""


class DoneSignal(Exception):
    """Control flow exception to exit the tool loop."""

    def __init__(self, payload: DonePayload):
        self.payload = payload
        super().__init__(f"done({payload.outcome})")


@dataclass
class ProveGoalV2State:
    """Accumulated state for a prove_goalv2 run.

    Tool closures append to proofs/sketches/lemmas. _v2_finalize reads
    them to pick the best outcome and reconstruct the proof with helpers.
    """

    proofs: list[ProofSubmission] = field(default_factory=list)
    sketches: list[SketchSubmission] = field(default_factory=list)
    lemmas: list[LemmaRegistration] = field(default_factory=list)
    done_payload: DonePayload | None = None
    iteration: int = 0
    max_iterations: int = 20
    get_reasoning_calls: int = 0
    lean_explore_calls: int = 0
    stuck_done_requests: int = 0

    @property
    def turns_left(self) -> int:
        """Remaining tool-loop iterations after the current one."""
        return max(0, self.max_iterations - self.iteration - 1)

    @property
    def active_lemmas(self) -> list[LemmaRegistration]:
        """Lemmas currently loaded in context, in registration order."""
        return [l for l in self.lemmas if l.active]

    @property
    def best_proof(self) -> ProofSubmission | None:
        """Most recent typechecking proof."""
        for p in reversed(self.proofs):
            if p.typechecks:
                return p
        return None

    @property
    def best_sketch(self) -> SketchSubmission | None:
        """Most recent valid sketch with extractable subgoals."""
        for s in reversed(self.sketches):
            if s.has_valid_subgoals:
                return s
        return None
