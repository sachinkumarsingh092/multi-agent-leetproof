from __future__ import annotations

import asyncio
import logging
import re
from contextlib import asynccontextmanager
from dataclasses import dataclass
from typing import Any, Awaitable, Callable, Dict, List, Optional, Tuple

import sexpdata

logger = logging.getLogger(__name__)

from pantograph.data import CompilationUnit, SearchTarget
from utils.proof_types import ExistingPantographClient, PantographParams
from utils.lean.types import Goal, LakeBuildResult, LeanDiagnostic, Param
from utils.lean.goals import refine_suggestions
from utils.lean.normalization import normalize_extracted_goal_fields


@dataclass
class TacticResult:
    """Result of trying tactics against a sorried theorem."""
    success: bool
    tactic: str = ""
    proof: str = ""
    build_result: LakeBuildResult | None = None

from pantograph.server import Server, ServerError
from pantograph.expr import GoalState
from pantograph.message import Severity
from utils.lean.constants import PANTOGRAPH_CORE_OPTIONS

DEFAULT_OPTIONS = {
    "printDependentMVars": True,
    "printSorryGoals": True,
    "printExprAST": True,
}

DEFAULT_CORE_OPTIONS = list(PANTOGRAPH_CORE_OPTIONS)

_PRINT_DECL_KIND_RE = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(theorem|lemma|def|abbrev|example|instance|class|structure|inductive|opaque|axiom)\b"
)


class _LockedServerProxy:
    """Serialize all async Server method calls through the owning client."""

    def __init__(self, client: "PantographClient") -> None:
        self._client = client

    @property
    def proc(self):
        server = self._client._server
        return None if server is None else server.proc

    def __getattr__(self, name: str):
        async def _call(*args, **kwargs):
            return await self._client._call_server_method(
                name,
                *args,
                op_name=f"server.{name}",
                **kwargs,
            )

        return _call


class PantographClient:
    """Thin async wrapper around PyPantograph Server for prover-agent integration."""

    # Map notation to the head constant for inductiveness checks
    _INFIX_TO_HEAD: dict[str, str] = {
        "=": "Eq", "≠": "Ne", "∨": "Or", "∧": "And", "↔": "Iff",
        "≤": "LE.le", "≥": "GE.ge", "<": "LT.lt", ">": "GT.gt",
    }
    _PREFIX_TO_HEAD: dict[str, str] = {
        "∃": "Exists", "¬": "Not",
    }

    # Well-known types: skip inspect_symbol, use static knowledge.
    # Value is is_recursive (True → induction useful, False → only cases).
    _KNOWN_INDUCTIVE: dict[str, bool] = {
        "Nat": True, "Int": False, "List": True, "Bool": False,
        "Or": False, "And": False, "Eq": False, "Iff": False,
        "Option": False, "Exists": False, "Sigma": False,
        "True": False, "False": False, "Prod": False, "Sum": False,
        "Fin": False, "Subtype": False, "Ne": False,
    }
    _KNOWN_NON_INDUCTIVE: set[str] = {
        "Not", "LE.le", "GE.ge", "LT.lt", "GT.gt", "Prop", "Type", "Sort",
    }

    def __init__(
        self,
        *,
        imports: Optional[List[str]] = None,
        project_path: Optional[str] = None,
        options: Optional[Dict[str, Any]] = None,
        core_options: Optional[List[str]] = None,
        timeout: int = 60,
        buffer_limit: Optional[int] = 50_000_000,  # 50MB — grind diagnostics can produce very large responses
    ) -> None:
        self._imports = imports or ["Init"]
        self._project_path = project_path
        self._options = options or DEFAULT_OPTIONS
        self._core_options = core_options or DEFAULT_CORE_OPTIONS
        self._timeout = timeout
        self._buffer_limit = buffer_limit
        self._server: Optional[Server] = None
        self._server_lock = asyncio.Lock()
        self._server_proxy = _LockedServerProxy(self)
        # Exact global sequence of successful definition loads. This preserves
        # cross-key ordering for faithful replay after server restart.
        self._load_log: List[Tuple[str, str]] = []
        self._symbol_cache: Dict[str, dict] = {}
        self._inductive_cache: Dict[str, tuple[bool, bool]] = {}
        self._print_cache: Dict[str, str | None] = {}
        self.headers = "\n".join([f"import {imprt}" for imprt in self._imports])

    def close(self) -> None:
        """Kill the underlying Pantograph subprocess."""
        if self._server is not None:
            self._server._close()
            self._server = None

    def _server_is_alive(self) -> bool:
        """Check whether the cached Pantograph subprocess is still usable."""
        if self._server is None:
            return False
        proc = self._server.proc
        return proc is not None and proc.returncode is None

    async def _start_server(self) -> Server:
        logger.info("Initializing Pantograph Server (async)")
        server = await Server.create(
            imports=self._imports,
            project_path=self._project_path,
            options=self._options,
            core_options=self._core_options,
            timeout=self._timeout,
            buffer_limit=self._buffer_limit,
        )
        logger.info("Pantograph Server initialized successfully")
        return server

    async def _load_definitions_impl_unlocked(self, lean_code: str) -> None:
        server = await self._get_server_unlocked()
        await server.load_definitions_async(lean_code)

    async def _replay_load_log_unlocked(self) -> None:
        if not self._load_log:
            return
        logger.warning(
            "Replaying %d Pantograph definition load(s) after restart",
            len(self._load_log),
        )
        for key, lean_code in self._load_log:
            logger.info(f"[Pantograph] Replaying definitions for key '{key}':\n{lean_code}")
            await self._load_definitions_impl_unlocked(lean_code)

    async def _restart_and_replay_unlocked(self, reason: str) -> Server:
        logger.warning("Restarting Pantograph server: %s", reason)
        self.close()
        self._server = await self._start_server()
        self._symbol_cache.clear()
        self._inductive_cache.clear()
        self._print_cache.clear()
        await self._replay_load_log_unlocked()
        return self._server

    async def _run_with_server_recovery(
        self,
        operation: Callable[[Server], Awaitable[Any]],
        *,
        op_name: str,
    ) -> Any:
        """Run a Pantograph operation, restarting/replaying once if needed."""
        async with self._server_lock:
            for attempt in range(2):
                try:
                    server = await self._get_server_unlocked()
                    return await operation(server)
                except AssertionError as e:
                    if str(e) != "Server not running.":
                        raise
                    if attempt == 1:
                        raise RuntimeError(
                            f"Pantograph operation '{op_name}' failed after server restart: {e}"
                        ) from e
                    await self._restart_and_replay_unlocked(f"{op_name}: {e}")
                except ServerError as e:
                    if attempt == 1:
                        self._handle_server_crash(e)
                        raise RuntimeError(
                            f"Pantograph operation '{op_name}' failed after server restart: {e}"
                        ) from e
                    await self._restart_and_replay_unlocked(f"{op_name}: {e}")
            raise RuntimeError(f"Pantograph operation '{op_name}' exhausted recovery attempts")

    async def _call_server_method(
        self,
        method_name: str,
        *args: Any,
        op_name: str | None = None,
        **kwargs: Any,
    ) -> Any:
        return await self._run_with_server_recovery(
            lambda server: getattr(server, method_name)(*args, **kwargs),
            op_name=op_name or method_name,
        )

    def _handle_server_crash(self, error: Exception) -> None:
        """Handle a pantograph server crash by triggering graceful shutdown.

        Instead of letting the exception propagate to DBOS (which would mark
        the workflow as ERROR and break resumption), we trigger a graceful
        shutdown that leaves the workflow PENDING for clean resumption.
        """
        logger.error(f"Pantograph server crashed: {error}")
        logger.error("Triggering graceful shutdown to preserve workflow state for resumption.")
        self._server = None
        from utils.shutdown import request_shutdown, handle_shutdown_if_requested
        request_shutdown(f"Pantograph server crashed: {error}", run_hooks=False)
        handle_shutdown_if_requested("pantograph crash recovery")

    @staticmethod
    def _is_benign_inspect_error(error: Exception) -> bool:
        return (
            isinstance(error, ServerError)
            and (
                "Symbol not found" in str(error)
                or "expected a `Name`" in str(error)
            )
        )

    async def _get_server_unlocked(self) -> Server:
        """Get or create the Pantograph server. Caller must hold `_server_lock`."""
        try:
            if self._server_is_alive():
                return self._server

            if self._server is not None or self._load_log:
                logger.warning("Pantograph server unavailable; restarting and replaying definitions")
                self._server = await self._restart_and_replay_unlocked("cached server unavailable")
            else:
                self._server = await self._start_server()
            return self._server
        except ServerError as e:
            self._handle_server_crash(e)

    async def get_server(self) -> Server:
        """Get a serialized proxy for the Pantograph server (async)."""
        async with self._server_lock:
            await self._get_server_unlocked()
        return self._server_proxy

    async def restart(self) -> None:
        async with self._server_lock:
            await self._restart_and_replay_unlocked("explicit restart")

    async def gc(self) -> None:
        await self._run_with_server_recovery(
            lambda server: server.gc_async(),
            op_name="gc",
        )

    async def get_expr_type(self, expr: str)-> str :
        return await self._run_with_server_recovery(
            lambda server: server.expr_type_async(expr),
            op_name="expr_type",
        )

    async def load_definitions(self, key: str, lean_code: str) -> None:
        """Load Lean definitions into the Pantograph environment."""
        if not lean_code.strip():
            return

        logger.info(f"[Pantograph] Loading definitions for key '{key}':\n{lean_code}")
        await self._run_with_server_recovery(
            lambda server: server.load_definitions_async(lean_code),
            op_name=f"load_definitions[{key}]",
        )
        self._load_log.append((key, lean_code))

    async def load_and_discover_constants(self, key: str, lean_code: str) -> Tuple[LakeBuildResult | None, list[str]]:
        """Load definitions into env AND return names of newly introduced constants.

        Discovers constants first via check_compile (inheritEnv=False, so no
        redeclaration conflicts), then loads definitions into the environment.

        NOTE: For simplicity, this only loads everything if the entire code compiles, else, nothing is laoded to the environment
        """
        if not lean_code.strip():
            return (None,[])

        diagnostics, new_constants = await self._check_compile(lean_code)

        typechecks = not any(d.severity == "error" for d in diagnostics)
        if not typechecks:
            return (LakeBuildResult(typechecks=typechecks, diagnostics=diagnostics), [])

        # Now load into the environment
        await self.load_definitions(key, lean_code)

        return (None, new_constants)

    def get_load_log(self, predicate: Callable[[str], bool] | None = None) -> List[Tuple[str, str]]:
        """Return successful loads in exact global insertion order."""
        if predicate is None:
            return self._load_log.copy()
        return [(key, lean_code) for key, lean_code in self._load_log if predicate(key)]

    async def inspect_symbol(self, name: str) -> dict | None:
        """Inspect a Lean symbol via Pantograph.

        Returns None if the symbol is not found.

        The response includes the pretty-printed type, dependencies, and optional
        definition metadata. Practical classification heuristics based on keys:

        - Inductive/structure/typeclass: has `inductInfo`, usually no `value`
        - Constructor: has `constructorInfo`, usually no `value`
        - Def/theorem/lemma: has `value` and `valueDependency`
        - Opaque/axiom/builtin: may have `type` but no `value`

        Sample outputs (verbatim, truncated):

        - Inductive/structure (3 examples):
          `{'inductInfo': {'all': ['Nat'], 'ctors': ['Nat.zero', 'Nat.succ'], 'isNested': False, 'isRec': True, 'isReflexive': False, 'numIndices': 0, 'numParams': 0}, 'type': {'dependentMVars': [], 'pp': 'Type'}, 'typeDependency': []}`
          `{'inductInfo': {'all': ['List'], 'ctors': ['List.nil', 'List.cons'], 'isNested': False, 'isRec': True, 'isReflexive': False, 'numIndices': 0, 'numParams': 1}, 'type': {'dependentMVars': [], 'pp': 'Type u → Type u'}, 'typeDependency': []}`
          `{'inductInfo': {'all': ['Prod'], 'ctors': ['Prod.mk'], 'isNested': False, 'isRec': False, 'isReflexive': False, 'numIndices': 0, 'numParams': 2}, 'type': {'dependentMVars': [], 'pp': 'Type u → Type v → Type (max u v)'}, 'typeDependency': []}`
        - Constructor (3 examples):
          `{'constructorInfo': {'cidx': 1, 'induct': 'Nat', 'numFields': 1, 'numParams': 0}, 'type': {'dependentMVars': [], 'pp': 'Nat → Nat'}, 'typeDependency': ['Nat']}`
          `{'constructorInfo': {'cidx': 1, 'induct': 'List', 'numFields': 2, 'numParams': 1}, 'type': {'dependentMVars': [], 'pp': '{α : Type u} → α → List α → List α'}, 'typeDependency': ['List']}`
          `{'constructorInfo': {'cidx': 0, 'induct': 'Prod', 'numFields': 2, 'numParams': 2}, 'type': {'dependentMVars': [], 'pp': '{α : Type u} → {β : Type v} → α → β → α × β'}, 'typeDependency': ['Prod']}`
        - Def/theorem (2 examples):
          `{'type': {'dependentMVars': [], 'pp': '{α : Type u_1} → List α → Nat'}, 'typeDependency': ['List', 'Nat'], 'value': {'dependentMVars': [], 'pp': 'fun {α} x =>\n  List.brecOn x fun x f =>\n    (match (motive := (x : List α) → List.below x → Nat) x with\n      | [] => fun x => 0\n      | head :: as => fun x => x.1 + 1)\n      f'}, 'valueDependency': ['List', 'List.brecOn', 'Nat', 'List.below', 'List.length.match_1', 'Unit', 'List.nil', 'OfNat.ofNat', 'instOfNatNat', 'List.cons', 'HAdd.hAdd', 'instHAdd', 'instAddNat']}`
          `{'constructorInfo': {'cidx': 0, 'induct': 'True', 'numFields': 0, 'numParams': 0}, 'type': {'dependentMVars': [], 'pp': 'True'}, 'typeDependency': ['True']}`
        - Opaque/axiom/builtin (2 examples):
          `{'type': {'dependentMVars': [], 'pp': 'Nat'}, 'typeDependency': ['Nat']}`
          `{'type': {'dependentMVars': [], 'pp': 'Nat → Nat'}, 'typeDependency': ['Nat']}`

        Note:
        - `type` is a pretty-printed string (not a structured AST).
        - `print_result`, when present, is derived from `#print <name>` and
          contains the full info message emitted by Lean.
        """
        if name not in self._symbol_cache:
            try:
                async with self._server_lock:
                    for attempt in range(2):
                        try:
                            server = await self._get_server_unlocked()
                            info = await server.env_inspect_async(
                                name,
                                print_value=True,
                                print_dependency=True,
                            )
                            break
                        except ServerError as e:
                            if self._is_benign_inspect_error(e):
                                return None
                            if attempt == 1:
                                self._handle_server_crash(e)
                                raise RuntimeError(
                                    f"Pantograph operation 'inspect_symbol[{name}]' failed after server restart: {e}"
                                ) from e
                            await self._restart_and_replay_unlocked(f"inspect_symbol[{name}]: {e}")
                        except AssertionError as e:
                            if str(e) != "Server not running.":
                                raise
                            if attempt == 1:
                                raise RuntimeError(
                                    f"Pantograph operation 'inspect_symbol[{name}]' failed after server restart: {e}"
                                ) from e
                            await self._restart_and_replay_unlocked(f"inspect_symbol[{name}]: {e}")
                print_result = await self._get_printed_declaration(name)
                if print_result is not None:
                    info["print_result"] = print_result
                self._symbol_cache[name] = info
            except Exception:
                return None
        return self._symbol_cache[name]

    @staticmethod
    def _parse_printed_declaration(print_result: str) -> str | None:
        print_result = (print_result or "").strip()
        if not print_result:
            return None
        first_line = print_result.splitlines()[0].strip()
        return print_result if _PRINT_DECL_KIND_RE.match(first_line) is not None else None

    async def _get_printed_declaration(self, name: str) -> str | None:
        if name in self._print_cache:
            return self._print_cache[name]

        try:
            result = await self.check_build(f"#print {name}", include_info_logs=True)
        except Exception:
            self._print_cache[name] = None
            return None

        print_result = ""
        for diagnostic in result.diagnostics:
            if diagnostic.severity != "info":
                continue
            print_result = diagnostic.message.strip()
            if print_result:
                break

        parsed = self._parse_printed_declaration(print_result)
        self._print_cache[name] = parsed
        return parsed

    async def get_dependencies(self, name: str) -> list[str]:
        result = await self.inspect_symbol(name)
        if result is None:
            return []
        return result.get('valueDependency', [])

    # --- Type introspection helpers ---

    @staticmethod
    def _extract_type_head(type_str: str) -> str | None:
        """Heuristic: extract head constant from a pretty-printed Lean type.

        Returns a name suitable for ``inspect_symbol``, or None.
        """
        type_str = type_str.strip()
        if not type_str:
            return None
        if "→" in type_str or type_str.startswith("∀"):
            return None
        for op, head in PantographClient._INFIX_TO_HEAD.items():
            if f" {op} " in type_str:
                return head
        for op, head in PantographClient._PREFIX_TO_HEAD.items():
            if type_str.startswith(op):
                return head
        s = type_str.lstrip("(@")
        tokens = s.split()
        if tokens:
            head = tokens[0].rstrip(")")
            if head and head[0].isupper():
                return head
        return None

    @staticmethod
    def _sexp_head(parsed) -> str | None:
        """Extract the outermost head constant name from a parsed sexp.

        ``parsed`` comes from ``sexpdata.loads()``.  Recognises
        ``(:c Name)``, application ``((head) args…)``, and
        ``(:let name type value body)`` (recurses into body).
        """
        if isinstance(parsed, sexpdata.Symbol):
            return None
        if isinstance(parsed, (int, float, str)):
            return None
        if not isinstance(parsed, list) or not parsed:
            return None
        first = parsed[0]
        # (:c Name)
        if isinstance(first, sexpdata.Symbol) and first.value() == ':c' and len(parsed) >= 2:
            return str(parsed[1].value() if isinstance(parsed[1], sexpdata.Symbol) else parsed[1])
        # (:let name type value body)
        if isinstance(first, sexpdata.Symbol) and first.value() == ':let' and len(parsed) >= 5:
            return PantographClient._sexp_head(parsed[4])
        # Application: first element is the function
        return PantographClient._sexp_head(first)

    async def resolve_head_via_sexp(
        self,
        type_str: str,
        context_vars: list,
    ) -> str | None:
        """Use ``expr.echo`` with ``printExprAST`` to programmatically
        extract the head constant of a type expression.

        Builds a self-contained ``let`` expression from the goal's
        variable context so that local names resolve.
        """
        # Build let bindings for context variables
        parts: list[str] = []
        for v in context_vars:
            if v.name:
                parts.append(f"let {v.name} : ({v.t}) := sorry")
        let_expr = "; ".join(parts + [type_str]) if parts else type_str
        try:
            result = await self._run_with_server_recovery(
                lambda server: server.run_async('expr.echo', {"expr": let_expr}),
                op_name="resolve_head_via_sexp",
            )
            sexp_str = result.get("expr", {}).get("sexp")
            if not sexp_str:
                return None
            parsed = sexpdata.loads(sexp_str)
            return self._sexp_head(parsed)
        except Exception:
            return None

    async def check_inductive(
        self,
        type_str: str,
        context_vars: list | None = None,
    ) -> tuple[bool, bool]:
        """Check if a variable's type is inductive.

        Returns ``(is_inductive, is_recursive)``.

        Resolution order (fast → slow):
          1. Cache
          2. Static known-types map
          3. ``inspect_symbol`` on the type string / heuristic head
          4. ``expr.echo`` + sexp parsing for the precise head (needs context)
        """
        if type_str in self._inductive_cache:
            return self._inductive_cache[type_str]

        head = type_str.strip()
        candidates = [head]
        extracted = self._extract_type_head(head)
        if extracted and extracted != head:
            candidates.append(extracted)

        # --- Fast: static known types ---
        for candidate in candidates:
            if candidate in self._KNOWN_INDUCTIVE:
                result = (True, self._KNOWN_INDUCTIVE[candidate])
                self._inductive_cache[type_str] = result
                return result
            if candidate in self._KNOWN_NON_INDUCTIVE:
                self._inductive_cache[type_str] = (False, False)
                return (False, False)

        # --- Medium: inspect_symbol on candidates ---
        for candidate in candidates:
            info = await self.inspect_symbol(candidate)
            if info is not None and "inductInfo" in info:
                is_rec = info["inductInfo"].get("isRec", False)
                self._inductive_cache[type_str] = (True, is_rec)
                return (True, is_rec)

        # --- Slow: sexp-based resolution (precise head via expr.echo) ---
        if context_vars is not None:
            sexp_head = await self.resolve_head_via_sexp(type_str, context_vars)
            if sexp_head and sexp_head not in candidates:
                if sexp_head in self._KNOWN_INDUCTIVE:
                    result = (True, self._KNOWN_INDUCTIVE[sexp_head])
                    self._inductive_cache[type_str] = result
                    return result
                info = await self.inspect_symbol(sexp_head)
                if info is not None and "inductInfo" in info:
                    is_rec = info["inductInfo"].get("isRec", False)
                    self._inductive_cache[type_str] = (True, is_rec)
                    return (True, is_rec)

        self._inductive_cache[type_str] = (False, False)
        return (False, False)

    async def discover_user_constants(
        self,
        key: str,
        lean_code: str,
    ) -> tuple[list[str], list[str], list[str]]:
        """Load definitions and discover user constants and constructors.

        Returns (all_new_constants, user_constants, user_constructors).
        """
        all_new_constants = (await self.load_and_discover_constants(key, lean_code))[1]
        if not all_new_constants:
            return [], [], []

        # Keep only constants whose name appears in the source code the user wrote.
        # Auto-generated constants (casesOn, brecOn, rec, etc.) won't appear.
        user_constants = [c for c in all_new_constants if c in lean_code]

        # For user-defined inductives, grab their constructors via inspect_symbol.
        user_constructors: list[str] = []
        for c in user_constants:
            info = await self.inspect_symbol(c)
            if info is not None and "inductInfo" in info:
                ctors = info["inductInfo"].get("ctors", [])
                user_constructors.extend(ctors)

        logger.info(
            f"User constants (filtered {len(all_new_constants)} -> {len(user_constants)}): {user_constants}"
        )
        if user_constructors:
            logger.info(f"Discovered constructors: {user_constructors}")

        return all_new_constants, user_constants, user_constructors

    async def _check_compile(
        self,
        lean_code: str,
        diagnostics_severity: Optional[List[str]] = None,
    ) -> Tuple[list[LeanDiagnostic], list[str] ]:
        if diagnostics_severity is None:
            diagnostics_severity = ["info", "warning", "error"]
        results = await self._run_with_server_recovery(
            lambda server: server.check_compile_async(lean_code,new_constants=True),
            op_name="check_compile",
        )
        if not results:
            return ([],[])
        # Process all compilation units, not just the first
        diagnostics: list[LeanDiagnostic] = []
        new_constants : list[str] = []
        for unit in results:
            if unit.new_constants:
                new_constants.extend(unit.new_constants)
            for msg in unit.messages:
                d = self._message_to_diagnostics(msg, lean_code)
                if d.severity in diagnostics_severity:
                    diagnostics.append(d)
        return (diagnostics, new_constants)

    async def check_build(
        self,
        lean_code: str,
        include_info_logs: bool = False,
    ) -> LakeBuildResult:
        """Check Lean code and return LakeBuildResult (drop-in for lean_build_file_helper)."""
        severities = ["warning", "error"]
        if include_info_logs:
            severities.append("info")
        diagnostics = (await self._check_compile(lean_code, diagnostics_severity=severities))[0]
        typechecks = not any(d.severity == "error" for d in diagnostics)
        return LakeBuildResult(typechecks=typechecks, diagnostics=diagnostics)

    async def is_grindable(self, name: str) -> bool:
        """Check whether a declaration can be registered with `attribute [grind]`.

        This runs a lightweight compile check in the current Pantograph session
        environment with a single command:

            attribute [grind] <name>

        Returns True iff no error diagnostics are produced.
        """
        name = (name or "").strip()
        if not name:
            return False

        snippet = f"attribute [grind] {name}"
        diagnostics = (await self._check_compile(snippet, diagnostics_severity=["error"]))[0]
        return len(diagnostics) == 0

    async def load_sorry(
        self,
        lean_code: str,
    ) -> Optional[GoalState]:
        diagnostics = (await self._check_compile(lean_code, ["error"]))[0]
        if diagnostics:
            raise ValueError(
                "Code has errors, cannot load sorry:\n" + "\n".join(d.pp() for d in diagnostics)
            )
        targets = await self._run_with_server_recovery(
            lambda server: server.load_sorry_async(lean_code),
            op_name="load_sorry",
        )
        if len(targets) == 0:
            return None
        target: SearchTarget = targets[0]
        return target.goal_state

    async def extract_subgoals(
        self,
        lean_code: str,
        parent_name: str,
    ) -> tuple[list[Goal], Optional[GoalState]]:
        """Extract structured subgoals from code with sorry holes.

        Returns:
            Tuple of (goals, goal_state). goals is empty if no sorry found.
        """
        state = await self.load_sorry(lean_code)
        if state is None:
            return [], None
        goals = self.goals_from_state(state, prefix=parent_name)
        return goals, state

    @staticmethod
    def _goal_id_key(g) -> int:
        """Extract numeric suffix from Pantograph metavariable ID (e.g. '_uniq.1234' -> 1234)."""
        suffix = g.id.rsplit(".", 1)[-1]
        if not suffix.isdigit():
            raise ValueError(f"Unexpected Pantograph goal ID format: '{g.id}'")
        return int(suffix)

    @staticmethod
    def goals_from_state(state: GoalState, prefix: str) -> List[Goal]:
        # Sort by metavariable ID so goals follow textual sorry order.
        # Lean assigns _uniq.N IDs in declaration order.
        sorted_state_goals = sorted(state.goals, key=PantographClient._goal_id_key)
        goals = []
        for i, g in enumerate(sorted_state_goals):
            ghost = [v for v in g.variables if v.name and "✝" in v.name]
            if ghost:
                names = ", ".join(str(v.name) for v in ghost)
                logger.warning(
                    "Goal %d (%s) has ghost variables (dropping them): %s",
                    i, g.name or g.id, names,
                )
            raw_params = [
                Param(name=v.name, ty=v.t)
                for v in g.variables
                if v.name and "✝" not in v.name
            ]
            normalized_param_types, normalized_goal, normalized_case_tag = normalize_extracted_goal_fields(
                [param.ty for param in raw_params],
                g.target,
                g.name,
            )
            params = [
                Param(name=param.name, ty=normalized_param_types[j])
                for j, param in enumerate(raw_params)
            ]
            goals.append(Goal(
                name=f"{prefix}_{i}",
                params=params,
                final_goal=normalized_goal,
                case_tag=normalized_case_tag,
            ))
        return goals

    async def try_all_tactics(
        self,
        sorried_theorem: str,
        tactics: list[str],
    ) -> TacticResult:
        """Try a list of tactics against a theorem with exactly one sorry.

        Replaces the single ``sorry`` with each tactic in order and checks
        whether the result typechecks.  If a tactic contains ``exact?`` and
        Lean returns a "Try this" suggestion, the suggestion is substituted
        back and verified before being returned.

        Args:
            sorried_theorem: A Lean theorem containing exactly one ``sorry``.
            tactics: Candidate tactics to try, in priority order.

        Returns:
            A :class:`TacticResult` with ``success=True`` and the winning
            tactic/proof on the first match, or ``success=False`` if none work.

        Raises:
            ValueError: If *sorried_theorem* does not contain exactly one ``sorry``.
        """
        sorry_count = sorried_theorem.count("sorry")
        if sorry_count != 1:
            raise ValueError(
                f"Expected exactly 1 sorry in theorem, found {sorry_count}"
            )

        for tactic in tactics:
            candidate = sorried_theorem.replace("sorry", tactic, 1)
            logger.info(f"[try_all_tactics] Trying: {tactic}")

            result = await self.check_build(candidate, include_info_logs=True)
            logger.info(f"[try_all_tactics] {tactic} -> typechecks={result.typechecks}")

            if not result.typechecks:
                continue

            # Apply all "Try this" suggestions from ?-tactics (exact?, grind?, etc.)
            refined, refined_build = await refine_suggestions(
                candidate, result.diagnostics, self.check_build,
            )

            return TacticResult(
                success=True,
                tactic=tactic,
                proof=refined,
                build_result=refined_build or result,
            )

        return TacticResult(success=False)

    @staticmethod
    def _message_to_diagnostics(msg, code: str, context_lines: int = 3) -> LeanDiagnostic:
        severity_map = {
            Severity.INFORMATION: "info",
            Severity.WARNING: "warning",
            Severity.ERROR: "error",
        }
        severity = severity_map.get(msg.severity, "error")
        line = msg.pos.line
        column = msg.pos.column

        lines = code.splitlines()
        idx = line - 1
        line_content = lines[idx] if 0 <= idx < len(lines) else ""

        before_start = max(0, idx - context_lines)
        ctx_before = "\n".join(lines[before_start:idx]) if idx > 0 else ""

        after_end = min(len(lines), idx + 1 + context_lines)
        ctx_after = "\n".join(lines[idx + 1:after_end]) if idx + 1 < len(lines) else ""

        return LeanDiagnostic(
            severity=severity,
            message=msg.data,
            line=line,
            column=column,
            line_content=line_content,
            ctx_before=ctx_before,
            ctx_after=ctx_after,
        )


class PantographFactory:
    """Registry of PantographClient instances, keyed by session/problem ID."""

    _instances: Dict[str, PantographClient] = {}
    _default_key: str | None = None

    @classmethod
    def register(
        cls, key: str, client: PantographClient, make_default: bool = False
    ) -> None:
        logger.info(f"[PantographFactory] Registering client for key '{key}'. Current keys: {list(cls._instances.keys())}")
        cls._instances[key] = client
        if make_default:
            logger.info(f"[PantographFactory] Setting default client key to '{key}'")
            cls._default_key = key

    @classmethod
    def has(cls, key: str) -> bool:
        """Check if a client is registered for the given key."""
        return key in cls._instances

    @classmethod
    def get(cls, key: str) -> PantographClient:
        if key not in cls._instances:
            logger.error(f"[PantographFactory] Key '{key}' not found! Available keys: {list(cls._instances.keys())}")
            raise KeyError(f"No PantographClient registered for key '{key}'")
        return cls._instances[key]

    @classmethod
    def get_default_instance(cls) -> PantographClient:
        if cls._default_key is None:
            raise KeyError("No default PantographClient registered")
        return cls.get(cls._default_key)

    @classmethod
    def resolve_client(
        cls,
        *,
        source: PantographParams | ExistingPantographClient,
        make_default: bool = False,
    ) -> PantographClient:
        """Resolve a Pantograph client from an existing key or full params."""
        if isinstance(source, ExistingPantographClient):
            client = cls.get(source.key)
            if make_default:
                cls._default_key = source.key
            return client
        else:
            if cls.has(source.key):
                client = cls.get(source.key)
                if make_default:
                    cls._default_key = source.key
                return client

            client = PantographClient(
                imports=source.imports,
                project_path=source.project_path,
                options=source.options,
                core_options=source.core_options,
            )
            cls.register(source.key, client, make_default=make_default)
            return client

    @classmethod
    def cleanup(cls, key: str) -> None:
        if key in cls._instances:
            logger.info(f"[PantographFactory] Cleaning up client for key '{key}'. Remaining keys after: {[k for k in cls._instances.keys() if k != key]}")
            cls._instances[key].close()
            del cls._instances[key]
        else:
            logger.warning(f"[PantographFactory] Cleanup called for key '{key}' but not found. Current keys: {list(cls._instances.keys())}")

    @classmethod
    @asynccontextmanager
    async def session(cls, key: str, client: PantographClient):
        """Async context manager that registers a client and auto-cleans up on exit.

        Usage:
            async with PantographFactory.session(key, client) as pantograph:
                # use pantograph
            # automatically cleaned up
        """
        cls.register(key, client)
        try:
            yield client
        finally:
            cls.cleanup(key)
