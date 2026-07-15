"""
Proof search automation via symbol-guided MCTS.

Discovers symbols via Pantograph's inspect_symbol / valueDependency,
finds relevant lemmas via LeanExplore semantic search, generates
candidate tactics, and runs MCTS-based proof search with backtracking
and lightweight goal-structure guidance.
"""

from __future__ import annotations

import asyncio
import collections
import hashlib
import itertools
import json
import logging
import random
import re
import time
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from enum import Enum
from math import log, sqrt
from typing import TYPE_CHECKING, Callable, Any

from config.timeouts import Timeouts
from pantograph.expr import GoalState, Site
from pantograph.search import SearchState
from pantograph.server import ServerError, TacticFailure
from utils.lean.types import Goal, LakeBuildResult, Param
from utils.lean_explore_service import is_theorem_like_decl_type
from utils.lean_proof_parser import parse_lean_theorem

if TYPE_CHECKING:
    from tools.pantograph_client import PantographClient
    from tools.proof_search_viz import SearchTrace
    from utils.lean_explore_service import LeanExploreResult

logger = logging.getLogger(__name__)

GENERIC_PROOF_SYMBOLS: set[str] = {
    "ite", "dite", "decide", "id", "Function.comp",
    "Classical.choice", "Classical.em", "Classical.propDecidable",
    "congr", "congrArg", "congrFun", "rfl", "absurd",
}

GENERIC_EQ_SYMBOLS: set[str] = {"mp", "mpr", "symm", "trans", "refl"}
TYPECLASS_PROJECTION_RE = re.compile(r"\[self : ([A-Za-z0-9_'.]+)\b")



def _is_instance_like(name: str) -> bool:
    return bool(name) and (
        name.startswith("inst") or any(seg.startswith("inst") for seg in name.split('.'))
    )


def _is_theorem_like_result(result: LeanExploreResult) -> bool:
    """LeanExplore results must be enriched with declaration metadata."""
    if result.decl_type is None:
        raise RuntimeError(
            f"LeanExploreResult for '{result.name}' is missing decl_type; "
            "query-time enrichment is required"
        )
    return is_theorem_like_decl_type(result.decl_type)


def _printed_decl_header(info: dict) -> str | None:
    print_result = info.get("print_result")
    if not isinstance(print_result, str):
        return None
    return print_result.splitlines()[0].strip() or None


def _is_theorem_like_print_result(print_result: str) -> bool:
    return bool(
        re.match(
            r"^\s*(?:@\[[^\]]+\]\s*)*"
            r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
            r"(theorem|lemma)\b",
            print_result,
        )
    )


def _inspect_name(info: dict, fallback: str = "") -> str:
    """Pantograph often omits `name`; fall back to the queried symbol."""
    return info.get("name") or fallback


def _returns_universe(type_pp: str) -> bool:
    """Detect symbols whose result is a type universe rather than a theorem/data term."""
    target = type_pp.rsplit("→", 1)[-1].strip()
    return target == "Type" or target.startswith("Type ") or target.startswith("Sort")


def _is_typeclass_projection(name: str, type_pp: str) -> bool:
    """Detect projections like `HAdd.hAdd` from the instance argument in their type."""
    if not name or "." not in name or "[self :" not in type_pp:
        return False
    class_name = name.rsplit(".", 1)[0]
    match = TYPECLASS_PROJECTION_RE.search(type_pp)
    if match is None:
        return False
    return match.group(1) == class_name


def _is_generic_proof_symbol(name: str) -> bool:
    if not name:
        return False
    if name in GENERIC_PROOF_SYMBOLS:
        return True
    if name.startswith("Eq.") and name.split(".")[-1] in GENERIC_EQ_SYMBOLS:
        return True
    return False


def _structural_noise_reason(info: dict, fallback_name: str = "") -> str | None:
    """Pantograph-based reason for rejecting a generic or non-search-worthy symbol."""
    module = info.get("module")
    if module is None or "Lean" in module:
        return "lean_module"

    name = _inspect_name(info, fallback_name)
    if "Lean" in name:
        return "lean_name"

    if "inductInfo" in info:
        return "inductive_or_structure"
    if "constructorInfo" in info:
        return "constructor"

    type_pp = info.get("type", {}).get("pp", "")
    if _is_instance_like(name):
        return "instance_like"
    if _returns_universe(type_pp):
        return "returns_universe"
    if _is_typeclass_projection(name, type_pp):
        return "typeclass_projection"
    if _is_generic_proof_symbol(name):
        return "generic_proof_symbol"

    return None


def _is_relevant_discovered_lemma(
    result: LeanExploreResult,
    info: dict,
    *,
    fallback_name: str = "",
) -> tuple[bool, str | None]:
    """Final lemma filter using both LeanExplore metadata and Pantograph metadata.

    Decision order:
    1. Trust LeanExplore's enriched module metadata first for obvious internal noise.
    2. Normalize the Pantograph payload with the queried symbol name because
       `inspect_symbol()` often omits `info["name"]`.
    3. Apply the Pantograph structural-noise filter to reject inductives,
       constructors, instance-like declarations, typeclass projections, and
       generic proof combinators.
    """
    module_name = result.module_name
    if module_name is not None and "Lean" in module_name:
        return False, "leanexplore_module"

    normalized = {**info, "name": _inspect_name(info, fallback_name)}
    reason = _structural_noise_reason(normalized)
    return reason is None, reason


def _bullet_list(items: list[str], indent: str = "    ") -> str:
    """Render a readable bullet list for structured logging."""
    if not items:
        return f"{indent}- (none)"
    return "\n".join(f"{indent}- {item}" for item in items)


# ---------------------------------------------------------------------------
# Data types
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class RankedSymbol:
    """A symbol with its depth-weighted relevance score."""
    name: str
    score: float


class LemmaSelector(ABC):
    """Serializable selector for filtering/ordering lemma candidates.

    Subclass this and implement ``select()`` to create custom selectors.
    All subclasses must be picklable (no closures) for DBOS serialization.
    """

    @abstractmethod
    def select(self, lemmas: list[LeanExploreResult]) -> list[LeanExploreResult]:
        """Select/filter lemma candidates."""
        ...

    def __call__(self, lemmas: list[LeanExploreResult]) -> list[LeanExploreResult]:
        return self.select(lemmas)


class TopNSelector(LemmaSelector):
    """Keep the first *n* lemma candidates."""

    def __init__(self, n: int = 10):
        self.n = n

    def select(self, lemmas: list[LeanExploreResult]) -> list[LeanExploreResult]:
        return lemmas[:self.n]


@dataclass
class LemmaDiscoveryConfig:
    """Configuration for LeanExplore retrieval (query generation + fetching)."""
    top_n_symbols_for_lemma_discovery: int = 8
    results_per_query: int = 3
    batch_size: int = 8



@dataclass
class ProofSearchResult:
    """Result of an MCTS proof search attempt.

    Tactic recovery rationale
    -------------------------
    The flat tactic list recovered by ``recover_tactics()`` is a valid
    Lean tactic-mode proof because of three invariants maintained by
    the search loop:

    1. **Always goal[0].**  ``SearchState.next_goal_id`` returns 0
       because all priorities are initialised to 0.0 and ``max()``
       picks the first index.  This matches Lean's default tactic-mode
       behaviour of operating on the first goal.

    2. **auto_resume=True.**  Every ``goal_tactic_async`` call uses
       ``Site(goal_id, auto_resume=True)``.  This makes Pantograph
       return *all* open goals (no dormant/hidden goals), and new
       subgoals from branching tactics (``constructor``, ``cases``,
       ``induction``) appear depth-first at the front — exactly the
       order Lean's tactic mode uses.

    3. **Recorded tactic path.**  On success, the search reconstructs
       the tactic sequence from runtime metadata and stores it in
       ``_recovered_tactics``.  ``recover_tactics()`` returns that
       cached path.

    What could break this:
      - Changing ``next_goal_id`` to pick a non-zero goal would make
        the flat list invalid (tactics would target a different goal
        than Lean expects).  You'd need focus dots (``·``) or ``case``
        syntax to direct tactics.
      - Using ``auto_resume=False`` would hide dormant goals, making
        ``is_solved`` unreliable and changing goal ordering.
      - Failing to populate ``_recovered_tactics`` on solved search
        results would make recovery unavailable.
    """
    success: bool
    steps: int = 0
    duration: float = 0.0
    _solved_node: "SearchState | None" = field(default=None, repr=False)
    _recovered_tactics: list[str] | None = field(default=None, repr=False)
    trace: "SearchTrace | None" = field(default=None, repr=False)

    def recover_tactics(self) -> list[str] | None:
        """Recover the cached flat tactic sequence from a solved search."""
        if not self.success:
            return None
        if self._recovered_tactics is None:
            return None
        return list(self._recovered_tactics)

    def tactic_proof(self, sorry_theorem: str) -> str | None:
        """Build a valid tactic-mode proof from the recovered tactics.

        Returns the full theorem text with ``by`` + the flat tactic
        list, or None if recovery fails.
        """
        tactics = self.recover_tactics()
        if not tactics:
            return None
        header = sorry_theorem.split(":= by")[0].strip()
        body = "\n  ".join(tactics)
        return f"{header} := by\n  {body}\n"


class ValidatedTacticProofStatus(str, Enum):
    """Final status of search + tactic recovery + check_build."""

    SEARCH_FAILED = "search_failed"
    RECOVERY_FAILED = "recovery_failed"
    BUILD_FAILED = "build_failed"
    VERIFIED = "verified"


@dataclass
class ValidatedTacticProofResult:
    """Outcome of search + tactic recovery + check_build validation."""

    search_result: ProofSearchResult
    status: ValidatedTacticProofStatus = ValidatedTacticProofStatus.SEARCH_FAILED
    tactic_proof: str | None = None
    build_result: LakeBuildResult | None = None


def goal_from_sorry_theorem(sorry_theorem: str) -> Goal:
    """Parse a theorem-with-sorry string into a Goal object."""
    parsed = parse_lean_theorem(sorry_theorem)
    if not parsed.return_type:
        raise ValueError("Theorem has no return type")

    params: list[Param] = []
    for binder in parsed.params:
        for name in binder.names:
            if name:
                params.append(Param(name=name, ty=binder.type_expr))

    return Goal(name=parsed.name, params=params, final_goal=parsed.return_type)


# ---------------------------------------------------------------------------
# Symbol discovery and ranking
# ---------------------------------------------------------------------------

async def build_dependency_graph(
    pantograph_client: PantographClient,
    constants: list[str],
    max_depth: int = 1,
) -> dict[str, list[str]]:
    """BFS over valueDependency up to max_depth."""
    graph: dict[str, list[str]] = {}
    visited: set[str] = set()
    queue = collections.deque((c, 0) for c in constants)

    while queue:
        sym, depth = queue.popleft()
        if sym in visited or depth > max_depth:
            continue
        visited.add(sym)
        try:
            deps = await pantograph_client.get_dependencies(sym)
        except Exception:
            deps = []
        graph[sym] = deps
        if depth < max_depth:
            for dep in deps:
                if dep not in visited:
                    queue.append((dep, depth + 1))
    return graph


async def rank_symbols(
    roots: list[str],
    dep_graph: dict[str, list[str]],
    pantograph_client: PantographClient | None = None,
    is_relevant: Callable[[dict], bool] | None = None,
) -> list[RankedSymbol]:
    """Depth-weighted frequency ranking + optional Pantograph relevance filtering."""
    scores: dict[str, float] = collections.defaultdict(float)

    for root in roots:
        visited: set[str] = set()
        queue = collections.deque([(root, 1)])
        while queue:
            sym, depth = queue.popleft()
            if sym in visited:
                continue
            visited.add(sym)
            scores[sym] += 1.0 / depth
            for dep in dep_graph.get(sym, []):
                if dep not in visited:
                    queue.append((dep, depth + 1))

    ranked = [RankedSymbol(name, score)
              for name, score in sorted(scores.items(), key=lambda x: x[1], reverse=True)]

    if pantograph_client is not None:
        ranked = await filter_search_relevant(ranked, pantograph_client, is_relevant)

    return ranked


# ---------------------------------------------------------------------------
# Lemma discovery and tactic pool building
# ---------------------------------------------------------------------------

def default_query_generator(symbols: list[str]) -> list[str]:
    """Generate search queries from symbol combinations.

    Override this to customize how LeanExplore queries are built.
    """
    queries: list[str] = []
    for a, b in itertools.combinations(symbols, 2):
        queries.append(f"{a} {b}")
    for s in symbols[:5]:
        queries.append(s)
    for a, b, c in list(itertools.combinations(symbols[:5], 3))[:4]:
        queries.append(f"{a} {b} {c}")
    return queries


async def discover_lemmas(
    ranked_symbols: list[RankedSymbol],
    config: LemmaDiscoveryConfig,
    query_generator: Callable[[list[str]], list[str]] = default_query_generator,
) -> list[LeanExploreResult]:
    """Find relevant lemmas via LeanExplore semantic search.

    Args:
        ranked_symbols: Symbols ranked by relevance.
        config: Retrieval parameters (defaults to LemmaDiscoveryConfig()).
        query_generator: Function that takes symbol names and returns
            search query strings. Override to customize query strategy.
    """
    from utils.lean_explore_service import semantic_search

    cfg = config
    ranked_names = [s.name for s in ranked_symbols]
    query_symbols = (
        ranked_names[:cfg.top_n_symbols_for_lemma_discovery]
        if cfg.top_n_symbols_for_lemma_discovery > 0
        else ranked_names
    )
    seen: set[str] = set()
    lemmas: list[LeanExploreResult] = []

    query_failures = 0
    query_empty = 0
    raw_hits = 0
    duplicate_hits = 0

    async def _search_and_collect(query: str) -> None:
        nonlocal query_failures, query_empty, raw_hits, duplicate_hits
        try:
            results = await semantic_search(
                query=query, num_results=cfg.results_per_query, verify=False,
            )
            raw_hits += len(results)
            if not results:
                query_empty += 1

            for r in results:
                if r.name and r.name not in seen:
                    seen.add(r.name)
                    lemmas.append(r)
                elif r.name:
                    duplicate_hits += 1
        except Exception:
            query_failures += 1

    queries = query_generator(query_symbols)
    for i in range(0, len(queries), cfg.batch_size):
        batch = queries[i:i + cfg.batch_size]
        await asyncio.gather(*[_search_and_collect(q) for q in batch])

    logger.info(
        "[LEMMA_DISCOVERY_DONE]\n"
        "  Ranked symbol count: %d\n"
        "  Top-N symbols for lemma discovery: %d (<=0 means use all)\n"
        "  Symbols used for query generation:\n%s\n"
        "  Query count: %d\n"
        "  Results/query: %d\n"
        "  Batch size: %d\n"
        "  Unique lemmas: %d\n"
        "  Raw hits: %d\n"
        "  Duplicate hits: %d\n"
        "  Empty queries: %d\n"
        "  Failed queries: %d\n"
        "  Unique lemma names:\n%s",
        len(ranked_symbols),
        cfg.top_n_symbols_for_lemma_discovery,
        _bullet_list(query_symbols),
        len(queries),
        cfg.results_per_query,
        cfg.batch_size,
        len(lemmas),
        raw_hits,
        duplicate_hits,
        query_empty,
        query_failures,
        _bullet_list([l.name for l in lemmas]),
    )
    return lemmas


async def filter_lemmas(
    lemmas: list[LeanExploreResult],
    pantograph_client: PantographClient,
    select: LemmaSelector,
) -> list[LeanExploreResult]:
    """Filter discovered lemmas to keep only useful theorem/lemma declarations.

    Returns filtered LeanExploreResult objects.

    Filtering stages:
    1. LeanExplore metadata must classify the result as a theorem.
    2. Pantograph must be able to inspect the symbol in the current project context.
    3. Pantograph `#print` metadata, when available, must agree that the
       declaration is theorem-like.
    4. The combined lemma predicate rejects internal/module noise first using
       LeanExplore metadata, then applies Pantograph structural filtering.
    5. The caller-provided selector performs the final trimming/ranking step.

    Args:
        lemmas: Raw results from ``discover_lemmas``.
        pantograph_client: Client for inspecting symbol types.
        select: Post-filter selector (e.g. ``TopNSelector(30)``).
    """
    filtered: list[LeanExploreResult] = []

    drop_counts = collections.Counter()
    drop_names: dict[str, list[str]] = collections.defaultdict(list)

    def _drop(reason: str, name: str) -> None:
        drop_counts[reason] += 1
        drop_names[reason].append(name)

    for r in lemmas:
        # Stage 1: LeanExplore query-time enrichment already classified the declaration.
        if not _is_theorem_like_result(r):
            _drop("non_theorem_lemma", r.name)
            continue

        # Stage 2: verify the symbol resolves in the active Pantograph session.
        info = await pantograph_client.inspect_symbol(r.name)
        if info is None:
            _drop("inspect_missing", r.name)
            continue

        name = _inspect_name(info, r.name)

        # Stage 3: trust parsed `#print` headers when Pantograph surfaces them.
        print_result = _printed_decl_header(info)
        if print_result is not None and not _is_theorem_like_print_result(print_result):
            _drop("print_non_theorem_lemma", name)
            logger.info(
                "[LEMMA_FILTER_DECISION] lemma=%s result=dropped stage=print print_result=%s",
                name,
                print_result,
            )
            continue

        # Stage 4: combine LeanExplore metadata with Pantograph structure.
        is_relevant, reason = _is_relevant_discovered_lemma(r, info, fallback_name=r.name)
        if not is_relevant:
            _drop("internal_or_instance_like", name)
            logger.info(
                "[LEMMA_FILTER_DECISION] lemma=%s result=dropped stage=combined reason=%s",
                name,
                reason or "unknown",
            )
            continue

        filtered.append(r)
        logger.info("[LEMMA_FILTER_DECISION] lemma=%s result=kept", name)

    selected = select(filtered)
    selector_dropped = max(len(filtered) - len(selected), 0)

    logger.info(
        "[LEMMA_FILTER_DROP_NAMES]\n"
        "  Input lemmas: %d\n"
        "  Theorem/lemma candidates: %d\n"
        "  Kept after selector: %d\n"
        "  Dropped by selector: %d\n"
        "  Kept names:\n%s\n"
        "  Dropped names by reason:\n"
        "    - non_theorem_lemma: %s\n"
        "    - inspect_missing: %s\n"
        "    - print_non_theorem_lemma: %s\n"
        "    - internal_or_instance_like: %s",
        len(lemmas),
        len(filtered),
        len(selected),
        selector_dropped,
        _bullet_list([r.name for r in selected]),
        drop_names.get("non_theorem_lemma", []),
        drop_names.get("inspect_missing", []),
        drop_names.get("print_non_theorem_lemma", []),
        drop_names.get("internal_or_instance_like", []),
    )

    return selected


async def filter_grindable_lemmas(
    lemmas: list[LeanExploreResult],
    pantograph_client: PantographClient,
) -> list[LeanExploreResult]:
    """Keep only declarations that can be marked with `attribute [grind]`.

    Uses PantographClient.is_grindable() in the current session context.
    If the client does not expose is_grindable, returns input unchanged.
    """
    if not hasattr(pantograph_client, "is_grindable"):
        logger.info(
            "[GRIND_FILTER_SKIPPED]\n"
            "  Reason: Pantograph client does not expose is_grindable (legacy/mock client)\n"
            "  Returning input unchanged.\n"
            "  Input names:\n%s",
            _bullet_list([l.name for l in lemmas]),
        )
        return lemmas

    kept: list[LeanExploreResult] = []
    rejected_names: list[str] = []
    error_map: dict[str, str] = {}

    logger.info(
        "[GRIND_FILTER_START]\n"
        "  Input count: %d\n"
        "  Input names:\n%s",
        len(lemmas),
        _bullet_list([l.name for l in lemmas]),
    )

    for r in lemmas:
        try:
            if await pantograph_client.is_grindable(r.name):
                kept.append(r)
                logger.info("[GRIND_FILTER_DECISION] lemma=%s result=kept", r.name)
            else:
                rejected_names.append(r.name)
                logger.info("[GRIND_FILTER_DECISION] lemma=%s result=rejected", r.name)
        except Exception as e:
            msg = str(e).splitlines()[0][:200]
            error_map[r.name] = f"{type(e).__name__}: {msg}"
            logger.info(
                "[GRIND_FILTER_DECISION] lemma=%s result=error error_class=%s message=%s",
                r.name,
                type(e).__name__,
                msg,
            )

    logger.info(
        "[GRIND_FILTER_DONE]\n"
        "  Kept: %d\n"
        "  Rejected: %d\n"
        "  Errors: %d\n"
        "  Kept names:\n%s\n"
        "  Rejected names:\n%s\n"
        "  Error map: %s",
        len(kept),
        len(rejected_names),
        len(error_map),
        _bullet_list([l.name for l in kept]),
        _bullet_list(rejected_names),
        error_map,
    )
    return kept


def not_lean_internal(info: dict) -> bool:
    """Keep only symbols that look structurally useful for search."""
    return _structural_noise_reason(info) is None


async def filter_search_relevant(
    ranked_symbols: list[RankedSymbol],
    pantograph_client: PantographClient,
    is_relevant: Callable[[dict], bool] | None = None,
) -> list[RankedSymbol]:
    """Filter ranked symbols using ``is_relevant`` predicate on inspect_symbol info."""
    if is_relevant is None:
        return ranked_symbols
    result = []
    dropped_inspect_missing: list[str] = []
    dropped_irrelevant: list[str] = []
    dropped_reason_counts = collections.Counter()
    dropped_reason_names: dict[str, list[str]] = collections.defaultdict(list)
    for s in ranked_symbols:
        info = await pantograph_client.inspect_symbol(s.name)
        if info is None:
            dropped_inspect_missing.append(s.name)
            continue
        normalized = {**info, "name": _inspect_name(info, s.name)}
        if is_relevant(normalized):
            result.append(s)
        else:
            dropped_irrelevant.append(s.name)
            reason = _structural_noise_reason(normalized)
            if reason is not None:
                dropped_reason_counts[reason] += 1
                dropped_reason_names[reason].append(s.name)
            logger.info(
                "[RANK_FILTER_DECISION] symbol=%s result=dropped reason=%s",
                s.name,
                reason or "predicate_false",
            )

    logger.info(
        "[RANK_FILTER_DONE]\n"
        "  Kept: %d/%d\n"
        "  Kept names:\n%s\n"
        "  Dropped (inspect missing):\n%s\n"
        "  Dropped (predicate false):\n%s\n"
        "  Drop reasons: %s\n"
        "  Drop names by reason: %s",
        len(result),
        len(ranked_symbols),
        _bullet_list([s.name for s in result]),
        _bullet_list(dropped_inspect_missing),
        _bullet_list(dropped_irrelevant),
        dict(dropped_reason_counts),
        dict(dropped_reason_names),
    )
    return result


TACTIC_WEIGHT_TARGETED = 4.0   # goal-specific tactics (split on if/match)
TACTIC_WEIGHT_CORE = 3.0       # closers + user definitions
TACTIC_WEIGHT_STRUCTURAL = 2.0 # constructor, ext, push_neg, by_contra
TACTIC_WEIGHT_LEMMA = 0.5      # discovered lemma apply/rw


@dataclass(frozen=True)
class WeightedTactic:
    """A tactic paired with its base selection weight."""
    tactic: str
    base_weight: float


def build_tactic_pool(
    lemmas: list[str],
    user_constants: list[str] | None = None,
    user_constructors: list[str] | None = None,
) -> list[WeightedTactic]:
    """Generate candidate tactics from templates with base weights."""
    tactics: list[WeightedTactic] = []
    user_defs = user_constants or []
    user_ctors = user_constructors or []
    seen: set[str] = set()

    def _add(tactic: str, weight: float) -> None:
        if tactic not in seen:
            seen.add(tactic)
            tactics.append(WeightedTactic(tactic, weight))

    # Closers (avoid expensive tactics like aesop in MCTS baseline pool)
    for t in ["grind", "simp_all",
              "intros; expose_names; rfl",
              "intros; expose_names; assumption"]:
        _add(t, TACTIC_WEIGHT_CORE)

    # Structural openers
    for t in ["constructor <;> expose_names",
              "split <;> expose_names"]:
        _add(t, TACTIC_WEIGHT_STRUCTURAL)

    # User definitions — prefer simp-only rewrites over raw unfold.
    for d in user_defs:
        _add(f"simp only [{d}]", TACTIC_WEIGHT_CORE)
    if user_defs:
        all_defs = ", ".join(user_defs)
        _add(f"simp only [{all_defs}]", TACTIC_WEIGHT_CORE)
        _add(f"simp_all [{all_defs}]", TACTIC_WEIGHT_CORE)

    # Constructors
    for ctor in user_ctors:
        _add(f"apply {ctor}", TACTIC_WEIGHT_STRUCTURAL)

    # Discovered lemmas — individual apply/rw only
    for lem in lemmas:
        _add(f"apply {lem}", TACTIC_WEIGHT_LEMMA)
        _add(f"rw [{lem}]", TACTIC_WEIGHT_LEMMA)

    logger.info(f"Built tactic pool of {len(tactics)} tactics ({len(user_defs)} user defs, {len(lemmas)} lemmas)")
    return tactics


# ---------------------------------------------------------------------------
# ProofSearchMCTS — MCTS proof search
# ---------------------------------------------------------------------------


@dataclass
class _SearchRuntime:
    """Runtime-only per-node metadata for MCTS bookkeeping.

    Kept out of ``pantograph.search.SearchState`` to avoid monkey-patching
    undeclared attributes.
    """

    visit_count: int = 0
    exhausted: bool = False
    subtree_exhausted: bool = False
    tactic_applied: str | None = None


class ProofSearchMCTS:
    """MCTS proof search over Lean tactics.

    Uses Pantograph's SearchState for tree nodes.  The search loop is:
    1. **Select** — UCB1 walk from root to best leaf
    2. **Expand** — pick a tactic (weighted by goal structure), apply it
    3. **Estimate** 
    4. **Backup** — propagate value up the trajectory

    On success, the solved GoalState is stored for proof term extraction
    via ``goal_root``.
    """

    # In-process cache of prepare()-generated structural tactics.
    # Keyed by (goal target + non-ghost params) fingerprint.
    _prepare_cache: dict[str, tuple[tuple[str, float], ...]] = {}

    def __init__(
        self,
        tactic_pool: list[WeightedTactic],
        pantograph_client: PantographClient,
        c: float = 0.3,
    ):
        self.pantograph_client = pantograph_client
        self.c = c
        # Parallel lists of tactic strings and their selection weights.
        self._tactics: list[str] = [wt.tactic for wt in tactic_pool]
        self._weights: list[float] = [wt.base_weight for wt in tactic_pool]
        self._node_runtime: dict[int, _SearchRuntime] = {}

    @staticmethod
    def _returns_prop(type_pp: str) -> bool:
        """Best-effort semantic codomain check for proposition-valued heads."""
        if not isinstance(type_pp, str) or not type_pp.strip():
            return False
        s = type_pp.strip()
        for arrow in ("→", "->"):
            if arrow in s:
                s = s.rsplit(arrow, 1)[-1].strip()
        return s == "Prop"

    @staticmethod
    def _prepare_cache_key(goal_state: GoalState) -> str | None:
        """Fingerprint goal shape using target + non-ghost parameter signatures."""
        if not goal_state.goals:
            return None
        goal = goal_state.goals[0]
        payload = {
            "target": str(goal.target or ""),
            "params": [
                (v.name, str(v.t))
                for v in goal.variables
                if v.name and "✝" not in v.name
            ],
        }
        raw = json.dumps(payload, sort_keys=True, ensure_ascii=False)
        return hashlib.sha256(raw.encode("utf-8")).hexdigest()

    async def _resolve_head(self, type_str: str, context_vars: list) -> str | None:
        """Resolve elaborated head constant via Pantograph expr.echo sexp."""
        try:
            head = await self.pantograph_client.resolve_head_via_sexp(
                type_str,
                context_vars=context_vars,
            )
            if isinstance(head, str) and head.strip():
                return head.strip()
        except Exception:
            pass
        return None

    async def _inspect_head(self, head: str | None) -> dict[str, Any] | None:
        if not head:
            return None
        try:
            info = await self.pantograph_client.inspect_symbol(head)
            if isinstance(info, dict):
                return info
        except Exception:
            pass
        return None

    async def _var_meta(self, var, context_vars: list) -> tuple[bool, bool, bool, int]:
        """Return (is_prop, is_inductive, is_recursive, ctor_count) for a variable type."""
        type_str = str(var.t)

        head = await self._resolve_head(type_str, context_vars)
        info = await self._inspect_head(head)

        is_prop = False
        if info is not None:
            type_pp = info.get("type", {}).get("pp", "")
            is_prop = self._returns_prop(type_pp)

        is_ind, is_rec, ctor_count = False, False, 0

        if info is not None and "inductInfo" in info:
            ind = info.get("inductInfo") or {}
            if isinstance(ind, dict):
                is_ind = True
                is_rec = bool(ind.get("isRec", False))
                ctors = ind.get("ctors", [])
                if isinstance(ctors, list):
                    ctor_count = len(ctors)

        # Fallback to existing check_inductive API when head inspection failed.
        if not is_ind:
            try:
                chk = await self.pantograph_client.check_inductive(
                    type_str,
                    context_vars=context_vars,
                )
                if (
                    isinstance(chk, tuple)
                    and len(chk) == 2
                    and isinstance(chk[0], bool)
                    and isinstance(chk[1], bool)
                ):
                    is_ind, is_rec = chk
            except Exception:
                pass

        return is_prop, is_ind, is_rec, ctor_count

    async def _dependent_vars(self, goal_state: GoalState, var_name: str, variables: list, server) -> set[str]:
        """Names that disappear with `revert var_name` on the original state."""
        before = {v.name for v in variables if v.name}
        try:
            reverted = await server.goal_tactic_async(
                goal_state,
                f"revert {var_name}",
                site=Site(goal_id=0, auto_resume=True),
            )
        except Exception:
            return set()

        if not reverted.goals:
            return set()

        after = {v.name for v in reverted.goals[0].variables if v.name}
        return (before - after) - {var_name}

    async def prepare(self, goal_state: GoalState) -> None:
        """Prepare tactics with semantic filtering to avoid combinatorial blowups.

        Rules:
        - skip proposition-typed variables for structural tactics
        - skip single-constructor inductives
        - recursive inductives with >1 ctor: `induction x`
        - non-recursive inductives with >1 ctor: `cases x`
        - add `induction x generalizing y` only when `y` depends on `x`
          (detected by disappearance under `revert x`)

        A process-local cache keyed by goal target + non-ghost params is used
        to avoid repeating semantic analysis for recurring goal shapes.
        """
        if not goal_state.goals:
            return

        variables = goal_state.goals[0].variables
        seen = set(self._tactics)

        def _add(t: str, weight: float = TACTIC_WEIGHT_STRUCTURAL) -> None:
            if t not in seen:
                seen.add(t)
                self._tactics.append(t)
                self._weights.append(weight)

        cache_key = self._prepare_cache_key(goal_state)
        if cache_key is not None and cache_key in self._prepare_cache:
            cached = self._prepare_cache[cache_key]
            for tactic, weight in cached:
                _add(tactic, weight)
            logger.info(
                f"Prepared {len(self._tactics)} tactics for search "
                f"(cache hit, +{len(cached)} structural tactics)"
            )
            return

        from utils.lean.unused_var_removal import find_essential_vars

        server = await self.pantograph_client.get_server()
        essential = await find_essential_vars(goal_state, server)

        generated: list[tuple[str, float]] = []
        generated_seen: set[str] = set()

        def _emit(t: str, weight: float = TACTIC_WEIGHT_STRUCTURAL) -> None:
            if t not in generated_seen:
                generated_seen.add(t)
                generated.append((t, weight))
            _add(t, weight)

        data_essentials: set[str] = set()
        induction_vars: list[str] = []
        case_vars: list[str] = []

        for v in variables:
            if not v.name or "✝" in v.name or v.name not in essential:
                continue

            is_prop, is_ind, is_rec, ctor_count = await self._var_meta(v, variables)
            if is_prop:
                continue

            data_essentials.add(v.name)

            if not is_ind:
                continue
            if ctor_count <= 1:
                continue

            if is_rec:
                induction_vars.append(v.name)
                _emit(f"induction {v.name} <;> expose_names", TACTIC_WEIGHT_CORE)
            else:
                case_vars.append(v.name)
                _emit(f"cases {v.name} <;> expose_names", TACTIC_WEIGHT_STRUCTURAL)

        for x in induction_vars:
            deps = await self._dependent_vars(goal_state, x, variables, server)
            for y in sorted((deps & data_essentials) - {x}):
                _emit(
                    f"induction {x} generalizing {y} <;> expose_names",
                    TACTIC_WEIGHT_CORE,
                )

        if cache_key is not None:
            self._prepare_cache[cache_key] = tuple(generated)

        logger.info(
            f"Prepared {len(self._tactics)} tactics for search "
            f"(essential: {essential}, induction: {induction_vars}, cases: {case_vars}, "
            f"cache store: +{len(generated)} structural tactics)"
        )

    # --- Tree operations ---

    def _rt(self, state: SearchState) -> _SearchRuntime:
        """Get runtime metadata for a SearchState node."""
        key = id(state)
        if key not in self._node_runtime:
            self._node_runtime[key] = _SearchRuntime()
        return self._node_runtime[key]

    @staticmethod
    def _tested_tactic_strings(state: SearchState) -> list[str]:
        """Normalize tested_tactics to plain strings."""
        return [str(t) for t in (state.tested_tactics or [])]

    def _init_node(self, state: SearchState) -> SearchState:
        """Ensure MCTS bookkeeping values exist on a SearchState node."""
        state.total_value = float(state.total_value or 0.0)
        state.children = state.children or []
        state.tested_tactics = state.tested_tactics or []
        self._rt(state)
        return state

    def _backup(self, trajectory: list[SearchState], value: float):
        """Propagate value up the trajectory, updating visit counts."""
        for state in reversed(trajectory):
            rt = self._rt(state)
            state.total_value = float(state.total_value or 0.0) + value
            rt.visit_count += 1
            rt.subtree_exhausted = (
                rt.exhausted
                and all(self._rt(ch).subtree_exhausted for ch in (state.children or []))
            )

    def _estimate(self, state: SearchState) -> SearchState:
        """Assign value based on goal-count progress.

        Solved states get 1.0.  Unsolved states get a base value
        that rewards goal reduction but does NOT penalize goal
        increases — induction and split legitimately increase the
        goal count while being essential moves.  Small jitter
        breaks ties.
        """
        if state.goal_state.is_solved:
            state.total_value = 1.0
        else:
            parent_goals = len(state.parent.goal_state.goals) if state.parent else 1
            child_goals = len(state.goal_state.goals)
            if child_goals < parent_goals:
                # Goal count reduced — reward
                state.total_value = 0.2 + random.random() * 0.02
            else:
                # Same or increased (induction/split) — neutral baseline
                state.total_value = 0.1 + random.random() * 0.02
        return state

    def _select(self, state: SearchState) -> list[SearchState]:
        """UCB1 selection: walk tree from root to most promising leaf.

        Stops descending if the current node still has untested tactics
        and its children don't look clearly better (progressive
        widening). This ensures the search creates breadth, not just
        a single deep chain.
        """
        trajectory = [state]
        current = state

        while current.children:
            non_exhausted = [
                (i, child) for i, child in enumerate(current.children)
                if not self._rt(child).subtree_exhausted
            ]
            if not non_exhausted:
                return trajectory

            best_idx = non_exhausted[0][0]
            best_ucb = -float('inf')
            current_rt = self._rt(current)
            current_visits = max(current_rt.visit_count, 1)

            for i, child in non_exhausted:
                child_rt = self._rt(child)
                if child_rt.visit_count == 0:
                    # Unvisited child: select immediately (infinite UCB)
                    best_ucb = float('inf')
                    best_idx = i
                    break
                avg = float(child.total_value or 0.0) / child_rt.visit_count
                explore = self.c * sqrt(log(current_visits) / child_rt.visit_count)
                ucb = avg + explore
                if ucb > best_ucb:
                    best_ucb = ucb
                    best_idx = i

            # Progressive widening: if this node has untried tactics, stay
            # here with some probability rather than always diving deeper.
            # This ensures the search explores breadth at each node.
            if not current_rt.exhausted and current_rt.visit_count > 0:
                current_avg = float(current.total_value or 0.0) / current_rt.visit_count
                if best_ucb < current_avg + self.c:
                    return trajectory

            current = current.children[best_idx]
            trajectory.append(current)

        return trajectory

    # --- Tactic selection ---

    def _next_tactic(self, tested=None, goal_target: str = ""):
        """Weighted random tactic selection with goal-aware boosting.

        Dynamic adjustments:
        - ``split`` boosted when goal contains ``if`` or ``match``.
        - ``ext`` injected when goal contains both ``∀``/``fun`` and ``=``.
        """
        tested_set = set(tested) if tested else set()
        boost_split = "if " in goal_target or "match " in goal_target
        boost_ext = ("∀" in goal_target or "fun " in goal_target) and "=" in goal_target
        available: list[tuple[str, float]] = []
        for t, w in zip(self._tactics, self._weights):
            if t in tested_set:
                continue
            if boost_split and t.startswith("split"):
                w = TACTIC_WEIGHT_TARGETED
            available.append((t, w))
        # Dynamically inject ext when goal looks like extensionality
        if boost_ext and "ext <;> expose_names" not in tested_set:
            available.append(("ext <;> expose_names", TACTIC_WEIGHT_TARGETED))
        if not available:
            return None
        tactics, weights = zip(*available)
        return random.choices(tactics, weights=weights, k=1)[0]

    def _recover_tactics_from_node(self, node: SearchState) -> list[str]:
        """Recover flat tactic path from root→node using runtime metadata."""
        tactics: list[str] = []
        current = node
        while current.parent is not None:
            tactic = self._rt(current).tactic_applied
            if tactic is not None:
                tactics.append(tactic)
            current = current.parent
        tactics.reverse()
        return tactics

    def _viz_node_data(self, node: SearchState) -> dict[str, object]:
        """Node metadata payload for visualization serializer."""
        rt = self._rt(node)
        visit_count = rt.visit_count
        total_value = float(node.total_value or 0.0)
        avg_value = total_value / max(visit_count, 1)
        return {
            "tactic": rt.tactic_applied,
            "total_value": round(total_value, 4),
            "visit_count": visit_count,
            "avg_value": round(avg_value, 4),
            "exhausted": rt.exhausted,
            "subtree_exhausted": rt.subtree_exhausted,
            "tested_tactics": self._tested_tactic_strings(node),
        }

    # --- Search loop ---

    async def search(
        self,
        goal_state: GoalState,
        max_steps: int = 200,
        max_duration_seconds: float | None = None,
        trace: bool = False,
    ) -> ProofSearchResult:
        """Async MCTS proof search.

        Uses ``auto_resume=True`` so that ``GoalState.is_solved`` is
        correct (all goals visible, no hidden dormant goals) and
        tactic-path recovery sees the same goal ordering as Lean.

        Args:
            goal_state: Initial goal state from ``load_sorry``.
            max_steps: Maximum number of MCTS iterations.
            max_duration_seconds: Global wall-clock time budget for the whole
                search. ``None`` disables the timeout.
            trace: If True, record a step-by-step trace for visualization.
        """
        from tools.proof_search_viz import SearchTrace, serialize_tree

        server = await self.pantograph_client.get_server()
        await self.prepare(goal_state)
        time_start = time.time()

        _trace = SearchTrace() if trace else None
        # Snapshot the tactic pool (after prepare) for trace/viz
        tactic_pool_snapshot = [
            {"tactic": t, "weight": w}
            for t, w in zip(self._tactics, self._weights)
        ]

        root = self._init_node(SearchState(
            goal_state=goal_state,
            parent=None,
            parent_goal_id=None,
            priorities=[0.0 for _ in goal_state.goals],
        ))
        self._estimate(root)
        if _trace:
            _trace.assign_id(root)

        i_step = 0
        for i_step in range(max_steps):
            elapsed = time.time() - time_start
            if max_duration_seconds is not None and elapsed >= max_duration_seconds:
                logger.info(
                    "Search timed out after %.2fs at step %d",
                    elapsed,
                    i_step,
                )
                break

            trajectory = self._select(root)
            node = trajectory[-1]

            if node.goal_state.is_solved:
                dur = time.time() - time_start
                logger.info(f"Proof found in {i_step} steps ({dur:.2f}s)")
                if _trace:
                    _trace.record_step(i_step, trajectory, None, "solved")
                    _trace.metadata = {
                        "success": True, "steps": i_step, "duration": dur,
                        "tactic_pool": tactic_pool_snapshot,
                    }
                    tree_data = serialize_tree(root, _trace, node_data=self._viz_node_data)
                    _trace.metadata["tree"] = tree_data
                return ProofSearchResult(
                    success=True,
                    steps=i_step,
                    duration=dur,
                    _solved_node=node,
                    _recovered_tactics=self._recover_tactics_from_node(node),
                    trace=_trace,
                )

            goal_id = node.next_goal_id
            goal_target = node.goal_state.goals[0].target if node.goal_state.goals else ""
            tactic = self._next_tactic(self._tested_tactic_strings(node), goal_target=goal_target)

            if tactic is None:
                node_rt = self._rt(node)
                node_rt.exhausted = True
                node_rt.subtree_exhausted = all(
                    self._rt(child).subtree_exhausted for child in (node.children or [])
                )
                if _trace:
                    _trace.record_step(i_step, trajectory, None, "exhausted")
                if self._rt(root).subtree_exhausted:
                    logger.info(f"Search tree exhausted at step {i_step}")
                    break
                continue

            tested = node.tested_tactics or []
            tested.append(tactic)
            node.tested_tactics = tested
            try:
                next_goal_state = await server.goal_tactic_async(
                    node.goal_state, tactic, site=Site(goal_id, auto_resume=True),
                )

                child = self._init_node(SearchState(
                    goal_state=next_goal_state,
                    parent=node,
                    parent_goal_id=goal_id,
                    priorities=[0.0 for _ in next_goal_state.goals],
                ))
                self._rt(child).tactic_applied = tactic
                self._estimate(child)
                children = node.children or []
                children.append(child)
                node.children = children
                self._backup(trajectory, float(child.total_value or 0.0))
                if _trace:
                    _trace.assign_id(child)
                    _trace.record_step(
                        i_step,
                        trajectory,
                        tactic,
                        "success",
                        child,
                        child_value=float(child.total_value or 0.0),
                        child_goal_count=len(child.goal_state.goals) if child.goal_state else 0,
                        child_solved=bool(child.goal_state.is_solved) if child.goal_state else False,
                    )
            except TacticFailure:
                self._backup(trajectory, 0.0)
                if _trace:
                    _trace.record_step(i_step, trajectory, tactic, "failure")
            except ServerError as e:
                logger.warning(f"ServerError for tactic {tactic!r}: {e}")
                self._backup(trajectory, 0.0)
                if _trace:
                    _trace.record_step(i_step, trajectory, tactic, "error")
            except Exception as e:
                logger.warning(f"Unexpected error for tactic {tactic!r}: {e}")
                self._backup(trajectory, 0.0)
                if _trace:
                    _trace.record_step(i_step, trajectory, tactic, "error")
                if not server.proc:
                    logger.error("Pantograph server died, aborting search")
                    break

        dur = time.time() - time_start
        logger.info(f"Search failed after {i_step} steps ({dur:.2f}s)")
        if _trace:
            _trace.metadata = {
                "success": False, "steps": i_step, "duration": dur,
                "tactic_pool": tactic_pool_snapshot,
            }
            tree_data = serialize_tree(root, _trace, node_data=self._viz_node_data)
            _trace.metadata["tree"] = tree_data
        return ProofSearchResult(success=False, steps=i_step, duration=dur, trace=_trace)


# ---------------------------------------------------------------------------
# ProofSearcher — top-level orchestrator
# ---------------------------------------------------------------------------

class ProofSearcher:
    """Holds a Pantograph client and tactic pool for proof search."""

    def __init__(
        self,
        pantograph_client: PantographClient,
        tactic_pool: list[WeightedTactic] | None = None,
    ):
        self.client = pantograph_client
        self.tactic_pool: list[WeightedTactic] = tactic_pool or []

    async def search(
        self,
        goal: Goal,
        max_steps: int = 200,
        max_duration_seconds: float | None = Timeouts.PROOF_SEARCH,
        trace: bool = False,
    ) -> ProofSearchResult:
        """Run MCTS proof search for a single goal."""
        try:
            goal_state = await self.client.load_sorry(goal.as_sorried())
        except Exception as e:
            raise RuntimeError(
                f"Pantograph failed while loading goal state for proof search on {goal.name}"
            ) from e
        if goal_state is None:
            logger.warning(f"Failed to load sorry for goal: {goal.name}")
            return ProofSearchResult(success=False)

        agent = ProofSearchMCTS(self.tactic_pool, self.client)
        return await agent.search(
            goal_state,
            max_steps=max_steps,
            max_duration_seconds=max_duration_seconds,
            trace=trace,
        )

    async def search_validated_tactic_proof(
        self,
        goal: Goal,
        max_steps: int = 200,
        max_duration_seconds: float | None = Timeouts.PROOF_SEARCH,
        trace: bool = False,
    ) -> ValidatedTacticProofResult:
        """Search for a proof and validate recovered tactic proof with check_build."""
        result = await self.search(
            goal,
            max_steps=max_steps,
            max_duration_seconds=max_duration_seconds,
            trace=trace,
        )
        if not result.success:
            return ValidatedTacticProofResult(
                search_result=result,
                status=ValidatedTacticProofStatus.SEARCH_FAILED,
            )

        tactic_proof = result.tactic_proof(goal.as_sorried())
        if tactic_proof is None:
            return ValidatedTacticProofResult(
                search_result=result,
                status=ValidatedTacticProofStatus.RECOVERY_FAILED,
            )

        build_result = await self.client.check_build(tactic_proof)
        if not build_result.typechecks:
            return ValidatedTacticProofResult(
                search_result=result,
                status=ValidatedTacticProofStatus.BUILD_FAILED,
                tactic_proof=tactic_proof,
                build_result=build_result,
            )

        return ValidatedTacticProofResult(
            search_result=result,
            status=ValidatedTacticProofStatus.VERIFIED,
            tactic_proof=tactic_proof,
            build_result=build_result,
        )

    async def add_definitions(self, key: str, lean_code: str) -> list[str]:
        """Load new definitions/theorems into the Pantograph environment.

        Returns the names of newly introduced constants.
        """
        return (await self.client.load_and_discover_constants(key, lean_code))[1]

    def add_tactics(self, tactics: list[str], weight: float = TACTIC_WEIGHT_CORE) -> None:
        """Extend the tactic pool with new tactics (deduplicating)."""
        seen = {wt.tactic for wt in self.tactic_pool}
        for t in tactics:
            if t not in seen:
                seen.add(t)
                self.tactic_pool.append(WeightedTactic(t, weight))
