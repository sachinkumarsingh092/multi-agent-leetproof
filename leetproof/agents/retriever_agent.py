"""
RetrieverAgent - Handles hint retrieval for theorem proving.

Retrieval via LeanExplore (semantic):
1. LLM generates initial NLP query specs
2. LLM explores with `query_lean_explore`
3. LLM returns exact declaration names
4. We resolve those names directly and format final hints

Context provided to LLM:
- Informal reasoning (or sketch)
- The goal theorem
- Relevant context from the file
"""

import json
from enum import Enum
from dataclasses import dataclass, field
from typing import Optional, List, TYPE_CHECKING

from dbos import DBOS
from langchain_core.messages import HumanMessage, BaseMessage
from langchain_core.tools import tool

if TYPE_CHECKING:
    from providers import LLMConfig, ReasoningLevel
from langgraph.graph import StateGraph
from providers import ReasoningLevel

from agents.base import BaseAgent
from prompts.prompts import (
    SEMANTIC_QUERY_GEN_SYSTEM,
    RETRIEVER_EXPLORATION_SYSTEM,
)
from tools.pantograph_client import PantographClient, PantographFactory
from tools.proof_search import (
    build_dependency_graph,
    rank_symbols,
    discover_lemmas,
    filter_lemmas,
    filter_grindable_lemmas,
    not_lean_internal,
    LemmaDiscoveryConfig,
    TopNSelector,
    LemmaSelector,
)
from utils.lean_helpers import extract_lean_code_from_md_block
from utils.message_helpers import create_prompt, lean_block, section, stable
from utils.message_constants import AGENT_PROMPT
from utils.proof_types import (
    ExistingPantographClient,
    NewPantographClient,
    PantographParams,
    PantographSource,
    ProofHints,
)
from utils.lean_explore_service import (
    semantic_search,
    lookup_declarations_by_name,
    DEFAULT_LEANEXPLORE_PACKAGES,
    is_theorem_like_decl_type,
)
from logging_config import get_logger

logger = get_logger(__name__)


class SemanticDeclarationFilter(str, Enum):
    """Filter policy for goal-specific semantic hints."""

    THEOREMS_ONLY = "theorems_only"
    ALL = "all"


@dataclass
class RetrievalConfig:
    """Configuration for hint retrieval."""
    num_semantic_queries: int = 10
    semantic_results_per_query: int = 3
    semantic_package_filters: list[str] = field(
        default_factory=lambda: list(DEFAULT_LEANEXPLORE_PACKAGES)
    )
    semantic_declaration_filter: SemanticDeclarationFilter = (
        SemanticDeclarationFilter.THEOREMS_ONLY
    )


@dataclass
class DiscoveryConfig:
    """Configuration for Pantograph-based symbol/lemma discovery."""
    dep_graph_depth: int
    lemma_discovery: LemmaDiscoveryConfig
    select_lemmas: LemmaSelector = field(default_factory=TopNSelector)


@dataclass
class SemanticSearchSpec:
    """One LeanExplore semantic search request."""
    query: str
    num_results: int


# ============================================================================
# Helper Functions
# ============================================================================


def _parse_semantic_search_specs(
    parsed: object,
    *,
    default_num_results: int,
) -> List[SemanticSearchSpec]:
    """Parse semantic search specs from a decoded JSON array."""
    if not isinstance(parsed, list):
        return []

    specs = []
    for item in parsed:
        if not isinstance(item, dict):
            continue
        query = item.get("query")
        raw_num_results = item.get("num_results")
        num_results = (
            raw_num_results
            if isinstance(raw_num_results, int)
            else default_num_results
        )
        if (
            isinstance(query, str)
            and (query := query.strip())
            and isinstance(num_results, int)
            and num_results > 0
        ):
            specs.append(
                SemanticSearchSpec(
                    query=query,
                    num_results=num_results,
                )
            )
    return specs


def parse_queries_from_llm_response(
    llm_response: str,
    *,
    default_num_results: int,
) -> List[SemanticSearchSpec]:
    """Parse semantic search specs from a JSON array in the LLM response."""
    code_content = extract_lean_code_from_md_block(llm_response).strip()

    try:
        parsed = json.loads(code_content)
    except json.JSONDecodeError:
        logger.error("Failed to parse semantic search specs as JSON")
        return []

    specs = _parse_semantic_search_specs(
        parsed,
        default_num_results=default_num_results,
    )
    if not specs and not isinstance(parsed, list):
        logger.error("Semantic search specs must be a JSON array")
    return specs


def parse_symbol_selection_from_llm_response(llm_response: str) -> list[str]:
    """Parse a simple markdown bullet list of exact symbol names."""
    text = llm_response.strip()
    if not text:
        return []

    names: list[str] = []
    seen_names: set[str] = set()

    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line or line.startswith("```"):
            continue
        if line.startswith("- "):
            line = line[2:].strip()
        elif line.startswith("* "):
            line = line[2:].strip()
        else:
            continue

        # Accept only the symbol name before any explanation or code fence noise.
        name = line.split(":", 1)[0].strip().strip("`")
        if not name or " " in name or name in seen_names:
            continue

        seen_names.add(name)
        names.append(name)

    if not names:
        logger.error("Failed to parse final symbol selection as markdown bullet list")

    return names


def _format_exact_declaration_results(
    results: list,
    declaration_filter: SemanticDeclarationFilter,
) -> tuple[str, list[str]]:
    """Format resolved exact declarations for prover prompts."""
    exact_declarations: list[str] = []
    all_symbols: list[str] = []

    for result in results:
        if (
            declaration_filter == SemanticDeclarationFilter.THEOREMS_ONLY
            and not is_theorem_like_decl_type(result.decl_type)
        ):
            continue
        all_symbols.append(result.name)
        exact_declarations.append(f"- {result.name}: {result.statement or ''}")

    if not exact_declarations:
        return "", []

    return "# Goal-Specific Hints\n" + "\n".join(exact_declarations), all_symbols


# ============================================================================
# RetrieverAgent
# ============================================================================

@DBOS.dbos_class()
class RetrieverAgent(BaseAgent):
    """
    Agent that retrieves hints for theorem proving via semantic search (LeanExplore).
    """

    name = "retriever"
    description = "Generates targeted queries and retrieves hints for theorem proving"
    system_prompt = ""

    def __init__(self, config: "LLMConfig", config_name: Optional[str] = None, reasoning_level: "ReasoningLevel | None" = None):
        super().__init__(config, config_name=config_name, reasoning_level=reasoning_level)
        self._hints_cache: dict[str, ProofHints] = {}
        self._active_semantic_results_per_query = 3
        self._active_semantic_package_filters: tuple[str, ...] = DEFAULT_LEANEXPLORE_PACKAGES
        self._active_semantic_declaration_filter = SemanticDeclarationFilter.THEOREMS_ONLY
        self._active_validate_with: PantographParams | ExistingPantographClient | None = None

    def build_graph(self) -> StateGraph:
        raise NotImplementedError("Use retrieve_hints() directly")

    async def run_workflow(self, state: dict) -> dict:
        raise NotImplementedError("Use retrieve_hints() directly")

    def ensure_system_messages(self, messages: list[BaseMessage]) -> None:
        raise NotImplementedError("Each method uses its own prompts")

    async def get_tools(self) -> list:
        """Retriever-specific tools for interactive LeanExplore exploration."""
        default_results_per_query = self._active_semantic_results_per_query
        package_filters = self._active_semantic_package_filters
        declaration_filter = self._active_semantic_declaration_filter
        validate_with = self._active_validate_with

        @tool
        async def query_lean_explore(
            queries: list[str],
            num_results_per_query: int | None = None,
        ) -> str:
            """Run LeanExplore semantic search for one or more short natural-language queries.

            Returns exact declaration hits plus the related query themes that produced them.
            Use `queries` for the search texts and optionally set
            `num_results_per_query` to control how many results to fetch for each query.
            """
            effective_num_results = (
                num_results_per_query
                if isinstance(num_results_per_query, int) and num_results_per_query > 0
                else default_results_per_query
            )
            specs: list[SemanticSearchSpec] = []
            for query in queries:
                if isinstance(query, str) and query.strip():
                    specs.append(
                        SemanticSearchSpec(
                            query=query.strip(),
                            num_results=effective_num_results,
                        )
                    )
            formatted, _ = await self.execute_semantic_queries(
                specs,
                package_filters=package_filters,
                declaration_filter=declaration_filter,
                validate_with=validate_with,
            )
            return formatted or "No results found for those queries."

        return [query_lean_explore]

    async def _filter_results_available_in_env(
        self,
        results: list,
        *,
        validate_with: PantographParams | ExistingPantographClient | None,
    ) -> list:
        """Keep only declarations available in the active proving environment."""
        if validate_with is None or not results:
            return results

        try:
            client = PantographFactory.resolve_client(source=validate_with)
        except KeyError:
            logger.info(
                "Skipping semantic hint validation: Pantograph key '%s' is not active",
                validate_with.key,
            )
            return results

        available_results = []
        dropped_symbols: list[str] = []
        for result in results:
            info = await client.inspect_symbol(result.name)
            if info is None:
                dropped_symbols.append(result.name)
                continue
            available_results.append(result)

        if dropped_symbols:
            logger.info("Dropped unavailable semantic symbols: %s", dropped_symbols)

        return available_results

    # ========================================================================
    # Semantic (NLP) Retrieval via LeanExplore
    # ========================================================================

    async def generate_semantic_queries(
        self,
        goal_theorem: str,
        reasoning: str,
        relevant_context: str,
        num_queries: int = 10,
        default_num_results: int = 3,
    ) -> List[SemanticSearchSpec]:
        """Generate directed NLP queries using LLM."""
        prompt = create_prompt(
            task=stable("Generate semantic search queries to find relevant theorems for this proof"),
            sections=(
                section("Goal Theorem", stable(lean_block(goal_theorem))),
                section("Informal Reasoning", stable(reasoning if reasoning else "(Not provided)")),
                section(
                    "Relevant Context",
                    stable(lean_block(relevant_context) if relevant_context else "(Not available)"),
                ),
            ),
        )

        messages = [
            self.create_system_message(
                content=SEMANTIC_QUERY_GEN_SYSTEM,
                message_type=AGENT_PROMPT,
            ),
        ]
        self.append_prompt(messages, prompt)

        try:
            response = await self.ainvoke_llm(messages)
            queries = parse_queries_from_llm_response(
                response.content,
                default_num_results=default_num_results,
            )
            logger.info(
                "Generated semantic queries: %s",
                [f"{query.query} ({query.num_results})" for query in queries],
            )
            return queries[:num_queries]
        except Exception as e:
            logger.error(f"Failed to generate semantic queries: {e}")
            return []

    async def execute_semantic_queries(
        self,
        queries: List[SemanticSearchSpec],
        package_filters: tuple[str, ...] = DEFAULT_LEANEXPLORE_PACKAGES,
        declaration_filter: SemanticDeclarationFilter = SemanticDeclarationFilter.THEOREMS_ONLY,
        validate_with: PantographParams | ExistingPantographClient | None = None,
    ) -> tuple[str, List[str]]:
        """Execute semantic queries via LeanExplore and return exact declarations + symbol list."""

        if not queries:
            return "", []

        all_symbols = []
        exact_declarations = []
        seen_names = set()

        for search in queries:
            if len(search.query) < 10:
                continue

            try:
                hits = await semantic_search(
                    query=search.query,
                    num_results=search.num_results,
                    package_filters=list(package_filters),
                )
                hits = await self._filter_results_available_in_env(
                    hits,
                    validate_with=validate_with,
                )

                query_results = []
                for hit in hits:
                    if (
                        declaration_filter == SemanticDeclarationFilter.THEOREMS_ONLY
                        and not is_theorem_like_decl_type(hit.decl_type)
                    ):
                        continue
                    if hit.name not in seen_names:
                        seen_names.add(hit.name)
                        all_symbols.append(hit.name)
                        stmt = hit.statement or ""
                        query_results.append(f"- {hit.name}: {stmt}")

                if query_results:
                    exact_declarations.extend(query_results)

            except Exception as e:
                logger.info(f"Semantic query '{search.query}' failed: {e}")
                continue

        if not exact_declarations:
            return "", []

        formatted = "# Goal-Specific Hints\n" + "\n".join(exact_declarations)
        return formatted, all_symbols

    @DBOS.step()
    async def retrieve_semantic_hints(
        self,
        goal_theorem: str,
        reasoning: str,
        relevant_context: str,
        num_queries: int = 10,
        results_per_query: int = 3,
        package_filters: tuple[str, ...] = DEFAULT_LEANEXPLORE_PACKAGES,
        declaration_filter: SemanticDeclarationFilter = SemanticDeclarationFilter.THEOREMS_ONLY,
        validate_with: PantographParams | ExistingPantographClient | None = None,
    ) -> tuple[str, List[str]]:
        """Two-phase semantic retrieval with exploratory tool use and final synthesis."""
        self._active_semantic_results_per_query = results_per_query
        self._active_semantic_package_filters = package_filters
        self._active_semantic_declaration_filter = declaration_filter
        self._active_validate_with = validate_with

        try:
            initial_queries = await self.generate_semantic_queries(
                goal_theorem=goal_theorem,
                reasoning=reasoning,
                relevant_context=relevant_context,
                num_queries=num_queries,
                default_num_results=results_per_query,
            )

            exploration_prompt = create_prompt(
                task=stable("Explore LeanExplore results and refine toward the most useful exact declarations."),
                sections=(
                    section("Goal Theorem", stable(lean_block(goal_theorem))),
                    section("Informal Reasoning", stable(reasoning if reasoning else "(Not provided)")),
                    section(
                        "Relevant Context",
                        stable(
                            lean_block(relevant_context)
                            if relevant_context
                            else "(Not available)"
                        ),
                    ),
                    section(
                        "Initial Semantic Queries",
                        stable(
                            "\n".join(
                                f"- {query.query} ({query.num_results})"
                                for query in initial_queries
                            ) if initial_queries else "(None)"
                        ),
                    ),
                ),
                instructions=stable(
                    "Use `query_lean_explore` to test and refine queries. "
                    "Stop when you have a strong set of exact candidate declarations."
                ),
            )
            exploration_messages = [
                self.create_system_message(
                    content=RETRIEVER_EXPLORATION_SYSTEM,
                    message_type=AGENT_PROMPT,
                ),
            ]
            self.append_prompt(exploration_messages, exploration_prompt)
            exploration_response = await self.invoke_with_tools(
                exploration_messages,
                max_iterations=5,
            )
            exploration_messages.append(
                HumanMessage(
                    content=(
                        "Now return only the final exact declaration names as a markdown bullet list.\n\n"
                        "Rules:\n"
                        "- Return exact declaration names only.\n"
                        "- Choose names only from declarations that already appeared during exploration.\n"
                        "- One symbol per bullet.\n"
                        "- No explanations, no extra prose.\n\n"
                        "Example output:\n"
                        "- List.take_append_getElem\n"
                        "- List.drop_eq_getElem_cons\n"
                        "- Array.length_toList\n\n"
                        "Keep the final list compact and high-signal. Quality over quantity."
                    )
                )
            )
            final_response = await self.ainvoke_llm(
                exploration_messages,
                reasoning_level=ReasoningLevel.MEDIUM,
            )
            final_selector_output = self.extract_text(final_response)
            logger.info(
                "Final hint selector raw output:\n%s",
                final_selector_output,
            )
            selected_symbols = parse_symbol_selection_from_llm_response(
                final_selector_output,
            )
            exact_results = await lookup_declarations_by_name(
                selected_symbols,
                declaration_filter=declaration_filter.value,
            )
            exact_results = await self._filter_results_available_in_env(
                exact_results,
                validate_with=validate_with,
            )
            hints, symbols = _format_exact_declaration_results(
                exact_results,
                declaration_filter,
            )
            if not hints:
                logger.info(
                    "No exact symbols resolved from final selection; falling back to exploration query results"
                )
                hints, symbols = await self.execute_semantic_queries(
                    initial_queries,
                    package_filters=package_filters,
                    declaration_filter=declaration_filter,
                    validate_with=validate_with,
                )
            else:
                logger.info(f"Semantic symbols found: {symbols}")
                return hints, symbols
            logger.info(f"Semantic symbols found: {symbols}")
            return hints, symbols
        finally:
            self._active_semantic_results_per_query = 3
            self._active_semantic_package_filters = DEFAULT_LEANEXPLORE_PACKAGES
            self._active_semantic_declaration_filter = SemanticDeclarationFilter.THEOREMS_ONLY
            self._active_validate_with = None

    # ========================================================================
    # Pantograph-based Discovery
    # ========================================================================

    @DBOS.step()
    async def discover_proof_hints(
        self,
        source: PantographSource,
        code: str,
        config: DiscoveryConfig,
    ) -> ProofHints:
        """Discover user-defined symbols, dependencies, and relevant lemmas via Pantograph.

        Results are cached by code content — repeated calls with the same code
        skip the expensive discovery pipeline.
        """
        import hashlib
        cache_key = hashlib.sha256(code.encode()).hexdigest()
        if cache_key in self._hints_cache:
            logger.info("Discovery cache hit — reusing cached proof hints")
            return self._hints_cache[cache_key]

        if isinstance(source, NewPantographClient):
            owns_client = True
            client = PantographClient(
                project_path=source.project_path,
                imports=source.imports,
                options=source.options,
                core_options=source.core_options,
            )
            key = "discover"
        else:
            owns_client = False
            client = PantographFactory.get(source.key)
            key = source.key

        try:
            all_new, user_constants, user_constructors = await client.discover_user_constants(
                key, code,
            )

            dep_graph = await build_dependency_graph(
                client, all_new, max_depth=config.dep_graph_depth,
            )
            ranked = await rank_symbols(
                all_new, dep_graph, client, is_relevant=not_lean_internal,
            )

            raw_lemmas = await discover_lemmas(ranked, config=config.lemma_discovery)
            filtered_lemmas = await filter_lemmas(
                raw_lemmas, client, select=config.select_lemmas,
            )
            grindable_lemmas = await filter_grindable_lemmas(filtered_lemmas, client)

            ranked_names = [s.name for s in ranked]
            lemma_names = [l.name for l in filtered_lemmas]
            grindable_names = [l.name for l in grindable_lemmas]
            logger.info(
                f"Discovery complete:\n"
                f"  User constants:  {user_constants}\n"
                f"  User ctors:      {user_constructors}\n"
                f"  Ranked symbols:  {ranked_names}\n"
                f"  Lemmas (raw):    {[l.name for l in raw_lemmas]}\n"
                f"  Lemmas (filtered): {lemma_names}\n"
                f"  Lemmas (grindable): {grindable_names}"
            )

            hints = ProofHints(
                user_constants=user_constants,
                user_constructors=user_constructors,
                ranked_symbols=ranked_names,
                discovered_lemmas=filtered_lemmas,
                grindable_lemmas=grindable_names,
            )
            self._hints_cache[cache_key] = hints
            return hints
        finally:
            if owns_client:
                client.close()

    # ========================================================================
    # Main Entry Point
    # ========================================================================

    async def retrieve_hints(
        self,
        goal_theorem: str,
        relevant_context: str,
        informal_reasoning: Optional[str] = None,
        config: Optional[RetrievalConfig] = None,
        validate_with: PantographParams | ExistingPantographClient | None = None,
    ) -> str:
        """
        Retrieve hints for a goal theorem via semantic search.

        Args:
            goal_theorem: The theorem to prove
            relevant_context: Extracted file context (specs, definitions, etc.)
            informal_reasoning: Informal reasoning or proof sketch
            config: Configuration for retrieval (query counts, results per query)

        Returns:
            Hints string
        """
        if config is None:
            config = RetrievalConfig()

        logger.info(f"Retrieving hints for: {goal_theorem}")

        reasoning = informal_reasoning or ""

        hints, symbols = await self.retrieve_semantic_hints(
            goal_theorem, reasoning, relevant_context,
            num_queries=config.num_semantic_queries,
            results_per_query=config.semantic_results_per_query,
            package_filters=config.semantic_package_filters,
            declaration_filter=config.semantic_declaration_filter,
            validate_with=validate_with,
        )

        logger.info(f"Retrieved symbols: {symbols}")

        if not hints:
            logger.info("No hints found")
            return ""

        logger.info(f"Hints:\n{hints}")
        return hints
