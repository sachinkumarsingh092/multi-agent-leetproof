"""
Unified LeanExplore service for semantic search of Lean theorems.

This module provides a global singleton service for LeanExplore semantic search.
LeanExplore uses hybrid ranking combining:
- Semantic similarity (FAISS + sentence embeddings using BAAI/bge-base-en-v1.5)
- BM25+ lexical matching
- PageRank scores

LeanExplore provides semantic understanding of theorem meanings, making it
good for finding conceptually related theorems even when exact patterns differ.

Setup:
    1. pip install lean-xplore
    2. leanexplore data fetch  (downloads ~8GB of data)
    3. Call init_lean_service() before first use, or it auto-initializes lazily

Usage:
    from utils.lean_explore_service import semantic_search, get_semantic_hints

    # Optional: pre-initialize (otherwise happens on first search)
    await init_lean_service()

    # Search
    results = await semantic_search("commutativity of addition")

Configuration:
    - DISABLE_LEAN_EXPLORE: Set to "1", "true", or "yes" to disable LeanExplore
"""

import asyncio
import functools
import hashlib
import os
import re
import sqlite3
import subprocess
import threading
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple, cast
from config.timeouts import Timeouts
from utils.message_helpers import lean_block

# Fix Python 3.13 crash: tqdm's TqdmDefaultWriteLock.create_mp_lock() calls
# multiprocessing.RLock() which triggers resource_tracker._launch() → fork_exec()
# → "bad value(s) in fds_to_keep".  The original only catches ImportError/OSError.
# Monkey-patch create_mp_lock to also handle ValueError.
try:
    import tqdm.std as _tqdm_std
    _orig_create_mp_lock = _tqdm_std.TqdmDefaultWriteLock.create_mp_lock.__func__

    @classmethod
    def _safe_create_mp_lock(cls):
        if not hasattr(cls, 'mp_lock'):
            try:
                from multiprocessing import RLock
                cls.mp_lock = RLock()
            except (ImportError, OSError, ValueError):
                cls.mp_lock = None

    cast(Any, _tqdm_std.TqdmDefaultWriteLock).create_mp_lock = cast(Any, _safe_create_mp_lock)
except Exception:
    pass

from logging_config import get_logger

logger = get_logger(__name__)

DEFAULT_LEANEXPLORE_PACKAGES: tuple[str, str] = ("Init", "Mathlib")

# Thread pool for running synchronous LeanExplore calls
_executor = ThreadPoolExecutor(max_workers=2, thread_name_prefix="lean_explore")

# Global service instance (initialized lazily)
_service = None
_init_lock = asyncio.Lock()
_init_thread_lock = threading.Lock()
_search_thread_lock = threading.Lock()
_search_circuit_open = threading.Event()

_INSTANCE_PREFIX_RE = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*instance\b"
)
_CLASS_PREFIX_RE = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s*)*class\b"
)


class _LeanExploreDeclCategory(Enum):
    """Small classification used to suppress unhelpful search results."""
    THEOREM = "theorem"
    INSTANCE = "instance"
    CLASS = "class"
    DEFINITION = "definition"
    OTHER = "other"


def _classify_decl_category(
    *,
    name: str,
    decl_type: Optional[str],
    signature: str,
    is_projection: bool,
) -> _LeanExploreDeclCategory:
    """Classify a declaration into a small, typed search-relevance bucket.

    Rules:
    - `instance` signature, or `inst*` name: INSTANCE
    - projections stay in the DEFINITION bucket even if their enclosing
      statement text starts with `class`
    - `class` signature: CLASS
    - LeanExplore `decl_type == "theorem"`: THEOREM
    - LeanExplore `decl_type == "definition"`: DEFINITION
    - everything else: OTHER
    """
    if _INSTANCE_PREFIX_RE.match(signature) or name.startswith("inst"):
        return _LeanExploreDeclCategory.INSTANCE
    if is_projection and decl_type == "definition":
        return _LeanExploreDeclCategory.DEFINITION
    if _CLASS_PREFIX_RE.match(signature):
        return _LeanExploreDeclCategory.CLASS
    if decl_type == "theorem":
        return _LeanExploreDeclCategory.THEOREM
    if decl_type == "definition":
        return _LeanExploreDeclCategory.DEFINITION
    return _LeanExploreDeclCategory.OTHER


@dataclass(frozen=True)
class _LeanExploreDbMetadata:
    """Best-effort structured metadata derived from LeanExplore's local DB."""
    decl_type: Optional[str] = None
    module_name: Optional[str] = None
    is_internal: bool = False
    is_projection: bool = False
    category: _LeanExploreDeclCategory = _LeanExploreDeclCategory.OTHER


@dataclass
class LeanExploreResult:
    """A single LeanExplore search result.

    Fields:
        name: Fully qualified Lean name (e.g., "Nat.add_comm").
        statement: Display-friendly statement text (signature without proof body).
        source_file: Relative path in the Lean source tree (e.g., "Mathlib/Order/Monotone/Defs.lean").
        docstring: Lean doc-string attached to the declaration (present ~50% of the time).
        informal_description: AI-generated human-readable description (always present).
        decl_type: Declaration kind when known (e.g. "theorem", "definition").
        module_name: Lean module containing the declaration, when known.
    """

    name: str
    statement: str
    source_file: str
    docstring: Optional[str] = None
    informal_description: Optional[str] = None
    decl_type: Optional[str] = None
    module_name: Optional[str] = None


def is_theorem_like_decl_type(decl_type: str | None) -> bool:
    """Whether a LeanExplore declaration kind should count as theorem-like."""
    return decl_type in {"theorem", "lemma"}


@functools.lru_cache(maxsize=1)
def _lean_explore_db_columns() -> frozenset[str]:
    """Best-effort schema discovery for the local LeanExplore DB."""
    try:
        from lean_explore import defaults
    except ImportError:
        return frozenset()

    db_path = Path(defaults.DEFAULT_DB_PATH)
    if not db_path.exists():
        return frozenset()

    try:
        with sqlite3.connect(db_path) as conn:
            rows = conn.execute("PRAGMA table_info(declarations)").fetchall()
    except sqlite3.Error:
        return frozenset()

    return frozenset(str(row[1]) for row in rows)


def _required_declaration_columns() -> frozenset[str]:
    """Columns needed for query-time enrichment and filtering."""
    return frozenset({
        "lean_name",
        "decl_type",
        "module_name",
        "is_internal",
        "is_projection",
        "declaration_signature",
        "statement_text",
    })


@functools.lru_cache(maxsize=8192)
def _lookup_db_metadata(name: str) -> Optional[_LeanExploreDbMetadata]:
    """Best-effort lookup of useful LeanExplore declaration metadata."""
    if not name:
        return None

    columns = _lean_explore_db_columns()
    if not _required_declaration_columns().issubset(columns):
        return None

    try:
        from lean_explore import defaults
    except ImportError:
        return None

    db_path = Path(defaults.DEFAULT_DB_PATH)
    if not db_path.exists():
        return None

    try:
        with sqlite3.connect(db_path) as conn:
            row = conn.execute(
                """
                SELECT decl_type, module_name, is_internal, is_projection,
                       declaration_signature, statement_text
                FROM declarations
                WHERE lean_name = ?
                LIMIT 1
                """,
                (name,),
            ).fetchone()
    except sqlite3.Error:
        return None

    if row is None:
        return None

    signature = cast(Optional[str], row[4]) or cast(Optional[str], row[5]) or ""
    decl_type = cast(Optional[str], row[0])
    is_projection = bool(row[3])

    return _LeanExploreDbMetadata(
        decl_type=decl_type,
        module_name=cast(Optional[str], row[1]),
        is_internal=bool(row[2]),
        is_projection=is_projection,
        category=_classify_decl_category(
            name=name,
            decl_type=decl_type,
            signature=signature,
            is_projection=is_projection,
        ),
    )


def _exclude_enriched_result_reason(metadata: _LeanExploreDbMetadata) -> str | None:
    """Return the exact reason an enriched result should be excluded."""
    if metadata.is_internal:
        return "internal"
    if metadata.is_projection:
        return "projection"
    if metadata.category is _LeanExploreDeclCategory.INSTANCE:
        return "instance"
    if metadata.category is _LeanExploreDeclCategory.CLASS:
        return "class"
    return None


def _build_search_result(
    item: Any,
    metadata: _LeanExploreDbMetadata,
) -> LeanExploreResult:
    """Convert a LeanExplore API item plus optional DB metadata into our wrapper."""
    return LeanExploreResult(
        name=item.primary_declaration.lean_name or "",
        statement=item.display_statement_text or item.statement_text,
        source_file=item.source_file,
        docstring=item.docstring,
        informal_description=item.informal_description,
        decl_type=metadata.decl_type,
        module_name=metadata.module_name,
    )


def _module_name_to_source_file(module_name: str | None) -> str:
    """Best-effort conversion from module name to a source file path."""
    if not module_name:
        return ""
    return module_name.replace(".", "/") + ".lean"


@functools.lru_cache(maxsize=8192)
def _lookup_db_result(name: str) -> Optional[LeanExploreResult]:
    """Best-effort exact-name lookup from the local LeanExplore DB."""
    if not name:
        return None

    columns = _lean_explore_db_columns()
    if not _required_declaration_columns().issubset(columns):
        return None

    try:
        from lean_explore import defaults
    except ImportError:
        return None

    db_path = Path(defaults.DEFAULT_DB_PATH)
    if not db_path.exists():
        return None

    try:
        with sqlite3.connect(db_path) as conn:
            row = conn.execute(
                """
                SELECT decl_type, module_name, is_internal, is_projection,
                       declaration_signature, statement_text
                FROM declarations
                WHERE lean_name = ?
                LIMIT 1
                """,
                (name,),
            ).fetchone()
    except sqlite3.Error:
        return None

    if row is None:
        return None

    statement = cast(Optional[str], row[4]) or cast(Optional[str], row[5]) or ""
    return LeanExploreResult(
        name=name,
        statement=statement,
        source_file=_module_name_to_source_file(cast(Optional[str], row[1])),
        decl_type=cast(Optional[str], row[0]),
        module_name=cast(Optional[str], row[1]),
    )


def _is_disabled() -> bool:
    """Check if LeanExplore is disabled via environment variable."""
    return os.getenv("DISABLE_LEAN_EXPLORE", "").lower() in ("1", "true", "yes")


def _open_search_circuit(reason: str) -> None:
    """Disable optional semantic search after an infrastructure timeout."""
    if not _search_circuit_open.is_set():
        logger.error(
            "LeanExplore disabled for the remainder of this run: %s",
            reason,
        )
        _search_circuit_open.set()


def _check_memory() -> bool:
    """Check if there's enough memory to load LeanExplore.

    Returns:
        True if sufficient memory, False otherwise
    """
    try:
        import psutil

        mem = psutil.virtual_memory()
        available_gb = mem.available / (1024**3)
        total_gb = mem.total / (1024**3)

        logger.info(
            f"System memory: {available_gb:.1f} GB available / {total_gb:.1f} GB total ({mem.percent}% used)"
        )

        # LeanExplore needs: bge-base-en-v1.5 (~400MB) + FAISS index (~500MB-1GB) = ~1.5GB minimum
        MIN_REQUIRED_GB = 1.5

        if available_gb < MIN_REQUIRED_GB:
            logger.error("=" * 80)
            logger.error("❌ INSUFFICIENT MEMORY: Cannot load LeanExplore service")
            logger.error("=" * 80)
            logger.error(f"Available memory: {available_gb:.1f} GB")
            logger.error(f"Required minimum: {MIN_REQUIRED_GB:.1f} GB")
            logger.error("")
            logger.error("LeanExplore requires:")
            logger.error("  - bge-base-en-v1.5 model: ~400 MB")
            logger.error("  - FAISS index: ~500 MB - 1 GB")
            logger.error("  - Total: ~1.5 GB minimum")
            logger.error("")
            logger.error("Solutions:")
            logger.error("  1. Close other memory-intensive applications")
            logger.error("  2. Disable LeanExplore: export DISABLE_LEAN_EXPLORE=1")
            logger.error("  3. Increase system RAM or swap space")
            logger.error("")
            logger.error(
                "⚠ If the process gets killed (return code 137), it's the OOM killer."
            )
            logger.error("=" * 80)
            return False
        elif available_gb < MIN_REQUIRED_GB + 0.5:
            logger.warning("=" * 80)
            logger.warning(
                f"⚠ LOW MEMORY WARNING: Only {available_gb:.1f} GB available"
            )
            logger.warning("=" * 80)
            logger.warning("LeanExplore may fail to load or cause system instability.")
            logger.warning(
                "Recommended: Close other applications or disable LeanExplore."
            )
            logger.warning("=" * 80)

        return True

    except ImportError:
        logger.warning("psutil not installed, skipping memory check")
        return True
    except Exception as e:
        logger.warning(f"Failed to check memory: {e}")
        return True


def _init_service_sync():
    """Initialize the service synchronously (runs in thread pool)."""
    global _service
    if _service is not None:
        return

    with _init_thread_lock:
        if _service is not None:
            return

        _init_service_sync_inner()


def _init_service_sync_inner():
    """Actual initialization logic (must be called under _init_thread_lock)."""
    global _service

    if _is_disabled():
        logger.info(
            "LeanExplore disabled via DISABLE_LEAN_EXPLORE environment variable"
        )
        return

    # Check memory before attempting to load
    if not _check_memory():
        return

    try:
        from lean_explore.local.service import Service 

        logger.info(
            "Initializing LeanExplore service (loading embeddings and FAISS index)..."
        )
        logger.info("Note: LeanExplore uses bge-base-en-v1.5 for FAISS compatibility")
        logger.info("This may take 10-30 seconds and use ~1.5 GB of RAM...")

        _service = Service()
        logger.info("✓ LeanExplore service initialized successfully")

    except FileNotFoundError as e:
        logger.warning(f"LeanExplore data not available: {e}")
        logger.warning(
            "Run 'leanexplore data fetch' to download the required data (~8GB)"
        )
    except ImportError:
        logger.warning(
            "lean-xplore package not installed. Install with: pip install lean-xplore"
        )
    except MemoryError as e:
        logger.error("=" * 80)
        logger.error("❌ MEMORY ERROR: Not enough RAM to load LeanExplore service")
        logger.error("=" * 80)
        logger.error(f"Error details: {e}")
        logger.error("")
        logger.error("LeanExplore loads bge-base-en-v1.5 model (~400MB)")
        logger.error("Solutions:")
        logger.error("  1. Close other memory-intensive applications")
        logger.error("  2. Disable LeanExplore: export DISABLE_LEAN_EXPLORE=1")
        logger.error("  3. Increase system RAM")
        logger.error("=" * 80)
    except OSError as e:
        # Check for memory allocation errors
        if "cannot allocate memory" in str(e).lower() or "errno 12" in str(e).lower():
            logger.error("=" * 80)
            logger.error(
                "❌ MEMORY ALLOCATION ERROR: Cannot allocate memory for LeanExplore"
            )
            logger.error("=" * 80)
            logger.error(f"Error details: {e}")
            logger.error("")
            logger.error("Solutions:")
            logger.error("  1. Free up system memory (close applications)")
            logger.error("  2. Disable LeanExplore: export DISABLE_LEAN_EXPLORE=1")
            logger.error("  3. Increase swap space or system RAM")
            logger.error("=" * 80)
        else:
            logger.error(
                f"Failed to initialize LeanExplore service: {e}", exc_info=True
            )
    except RuntimeError as e:
        # Check for CUDA out of memory
        if "out of memory" in str(e).lower() or "cuda" in str(e).lower():
            logger.error("=" * 80)
            logger.error("❌ GPU MEMORY ERROR: Not enough VRAM for LeanExplore model")
            logger.error("=" * 80)
            logger.error(f"Error details: {e}")
            logger.error("")
            logger.error("LeanExplore will attempt to use CPU instead")
            logger.error("=" * 80)
        else:
            logger.error(
                f"Failed to initialize LeanExplore service: {e}", exc_info=True
            )
    except Exception as e:
        logger.error(f"Failed to initialize LeanExplore service: {e}", exc_info=True)


async def init_lean_service():
    """Initialize the LeanExplore service.

    This loads the embedding model and FAISS index into memory.
    Call this at startup to avoid initialization delay on first search.

    Can be called multiple times safely (only initializes once).
    """
    global _service
    if _service is not None:
        return

    if _is_disabled():
        return

    async with _init_lock:
        if _service is None:
            loop = asyncio.get_running_loop()
            await loop.run_in_executor(_executor, _init_service_sync)


async def get_lean_service():
    """Get the global LeanExplore service instance.

    Initializes the service if not already done.

    Returns:
        The Service instance, or None if disabled or failed to initialize
    """
    if _service is None and not _is_disabled():
        await init_lean_service()
    return _service


def is_initialized() -> bool:
    """Check if the LeanExplore service is initialized."""
    return _service is not None


def _ensure_service():
    """Ensure service is initialized (for sync contexts)."""
    global _service
    if _service is None and not _is_disabled():
        _init_service_sync()


def _source_file_to_import(source_file: str) -> str:
    """Convert source file path to import statement.

    Example:
        Mathlib/Data/PNat/Notation.lean -> Mathlib.Data.PNat.Notation
    """
    # Remove .lean extension and convert / to .
    if source_file.endswith('.lean'):
        source_file = source_file[:-5]
    return source_file.replace('/', '.')


async def _verify_theorem_exists(theorem_name: str, source_file: str, project_root: Path) -> Tuple[bool, str]:
    """Verify if a theorem exists in the local Mathlib by importing its specific module.

    Args:
        theorem_name: Name of the theorem (e.g., "Nat.add_comm")
        source_file: Source file path (e.g., "Mathlib/Data/Nat/Digits.lean")
        project_root: Path to the loom project directory

    Returns:
        (exists, error_message)
    """
    import_module = _source_file_to_import(source_file)

    # Create verification file in the project directory
    file_hash = hashlib.md5(theorem_name.encode()).hexdigest()[:8]
    test_file = project_root / f"_verify_{file_hash}.lean"

    try:
        # Write the verification file
        test_file.write_text(f"""import {import_module}

#check {theorem_name}
""")

        # Run lean on the file
        result = subprocess.run(
            ["lake", "env", "lean", str(test_file)],
            cwd=project_root,
            capture_output=True,
            text=True,
            timeout=30
        )

        # Check for errors in stderr
        stderr = result.stderr.lower()

        # Check for module/file not found errors
        if "object file" in stderr and "does not exist" in stderr:
            return False, f"Module {import_module} not built"

        if "unknown package" in stderr or "no such file" in stderr:
            return False, f"Module {import_module} not found"

        # Check for theorem not found errors
        if "unknown identifier" in stderr or "expected identifier" in stderr:
            # Extract a cleaner error message
            for line in result.stderr.split('\n'):
                if "unknown identifier" in line.lower() or "expected identifier" in line.lower():
                    return False, line.strip()
            return False, "Theorem not found"

        # If there's any error at all, consider it a failure
        if result.returncode != 0 or "error:" in stderr:
            # Extract the first error line for a cleaner message
            for line in result.stderr.split('\n'):
                if 'error:' in line.lower():
                    # Get just the error message, not the full path
                    error_msg = line.split('error:', 1)[1].strip() if 'error:' in line else line
                    return False, f"Error: {error_msg[:150]}"
            return False, "Build failed"

        return True, ""

    except subprocess.TimeoutExpired:
        return False, "Verification timeout"
    except Exception as e:
        return False, f"Verification error: {e}"
    finally:
        # Clean up the verification file
        test_file.unlink(missing_ok=True)


def _search_sync(
    query: str, num_results: int, package_filters: Optional[List[str]]
) -> List[LeanExploreResult]:
    """Synchronous search implementation."""
    if _search_circuit_open.is_set():
        return []

    _ensure_service()

    if _service is None:
        return []

    # LeanExplore's shared Service is not thread-safe. All callers, including
    # batched asyncio.gather users, must pass through this single-flight gate.
    with _search_thread_lock:
        if _search_circuit_open.is_set():
            return []
        response = _service.search(
            query=query,
            package_filters=package_filters,
            limit=num_results,
        )

    results = []
    drop_reason_counts: dict[str, int] = {}
    drop_reason_names: dict[str, list[str]] = {}
    for item in response.results:
        name = item.primary_declaration.lean_name or ""
        metadata = _lookup_db_metadata(name)
        if metadata is None:
            raise RuntimeError(
                f"LeanExplore DB enrichment missing for search result '{name}'"
            )
        reason = _exclude_enriched_result_reason(metadata)
        if reason is not None:
            drop_reason_counts[reason] = drop_reason_counts.get(reason, 0) + 1
            drop_reason_names.setdefault(reason, []).append(name)
            continue
        results.append(_build_search_result(item, metadata))

    logger.info(
        "[LEAN_EXPLORE_FILTER_DONE]\n"
        "  Query: %s\n"
        "  Returned: %d\n"
        "  Kept names: %s\n"
        "  Drop reasons: %s\n"
        "  Drop names by reason: %s",
        query,
        len(results),
        [r.name for r in results],
        drop_reason_counts,
        drop_reason_names,
    )
    return results


async def semantic_search(
    query: str,
    num_results: int = 10,
    package_filters: Optional[List[str]] = None,
    verify: bool = False,
    project_root: Optional[Path] = None,
) -> List[LeanExploreResult]:
    """Search for Lean theorems semantically.

    Performs semantic search using natural language queries.
    Describe what you're looking for conceptually.

    Examples of good queries:
    - "commutativity of addition for natural numbers"
    - "if a list is sorted and we insert an element, the result is sorted"
    - "empty list has length zero"
    - "composition of continuous functions is continuous"

    Args:
        query: Natural language description of the theorem you're looking for
        num_results: Maximum number of results to return (default: 10)
        package_filters: Optional list of packages to search (e.g., ["Mathlib", "Init"])
        verify: If True, verify each result exists in local Mathlib (default: False)
        project_root: Path to the Lean project root (where lakefile.lean/lakefile.toml lives).
            Required when verify=True. Use find_project_root() from utils.lean.build to obtain it.

    Returns:
        List of LeanExploreResult objects, sorted by relevance.
        Returns empty list if service is disabled or not available.
    """
    if _is_disabled() or _search_circuit_open.is_set():
        return []

    try:
        try:
            service = await asyncio.wait_for(
                get_lean_service(),
                timeout=Timeouts.LEAN_EXPLORE_INIT,
            )
        except TimeoutError:
            _open_search_circuit(
                f"initialization exceeded {Timeouts.LEAN_EXPLORE_INIT} seconds"
            )
            return []
        if service is None:
            return []

        loop = asyncio.get_running_loop()
        try:
            results = await asyncio.wait_for(
                loop.run_in_executor(
                    _executor,
                    _search_sync,
                    query,
                    num_results,
                    package_filters,
                ),
                timeout=Timeouts.LEAN_EXPLORE_SEARCH,
            )
        except TimeoutError:
            _open_search_circuit(
                f"search exceeded {Timeouts.LEAN_EXPLORE_SEARCH} seconds"
            )
            return []

        logger.debug(f"LeanExplore: '{query[:50]}...' -> {len(results)} results")

        # Verify results if requested
        if verify and results:
            if project_root is None:
                raise ValueError(
                    "project_root is required when verify=True. "
                    "Use find_project_root() from utils.lean.build to obtain it."
                )

            logger.info(f"Verifying {len(results)} results against local Mathlib...")
            verified_results = []
            removed_count = 0

            for result in results:
                exists, error = await _verify_theorem_exists(
                    result.name,
                    result.source_file,
                    project_root
                )

                if exists:
                    verified_results.append(result)
                else:
                    removed_count += 1
                    logger.debug(f"Removed {result.name}: {error}")

            logger.info(
                f"Verification complete: {len(verified_results)} verified, "
                f"{removed_count} removed"
            )
            return verified_results

        return results

    except ValueError:
        raise
    except Exception as e:
        logger.error(f"LeanExplore search failed: {e}")
        return []


async def lookup_declarations_by_name(
    names: List[str],
    declaration_filter: str | None = None,
) -> List[LeanExploreResult]:
    """Resolve exact declaration names from the local LeanExplore DB.

    This avoids semantic reranking when the caller already has exact symbols.
    Results preserve the input order and drop names not found in the DB.
    """
    results: list[LeanExploreResult] = []
    seen_names: set[str] = set()
    missing_names: list[str] = []
    missing_result_names: list[str] = []
    dropped_by_reason: dict[str, list[str]] = {}

    for raw_name in names:
        name = raw_name.strip()
        if not name or name in seen_names:
            continue

        metadata = _lookup_db_metadata(name)
        if metadata is None:
            missing_names.append(name)
            continue

        reason = _exclude_enriched_result_reason(metadata)
        if reason is not None:
            dropped_by_reason.setdefault(reason, []).append(name)
            continue

        if declaration_filter == "theorems_only" and not is_theorem_like_decl_type(
            metadata.decl_type
        ):
            dropped_by_reason.setdefault("decl_filter", []).append(name)
            continue

        result = _lookup_db_result(name)
        if result is None:
            missing_result_names.append(name)
            continue

        seen_names.add(name)
        results.append(result)

    return results
async def search_lean(
    query: str,
    limit: int = 20,
    filter_abbrev: bool = True,
    package_filters: Optional[List[str]] = None,
) -> List[Dict]:
    """Search Lean declarations with optional abbrev filtering.

    Args:
        query: Search query for Lean declarations
        limit: Number of results to return (after filtering if enabled)
        filter_abbrev: If True, filter out declarations containing 'abbrev'
        package_filters: Optional list of package names to filter results

    Returns:
        List of Lean declaration dictionaries with metadata.
        Returns empty list if service is disabled or not available.
    """
    # Fetch more results if filtering to account for filtered items
    fetch_limit = limit * 2 if filter_abbrev else limit

    results = await semantic_search(
        query=query,
        num_results=fetch_limit,
        package_filters=package_filters,
    )

    # Convert to dict format and optionally filter
    lean_decls = []
    for r in results:
        # Filter out abbrev declarations if requested
        if filter_abbrev and "abbrev" in r.statement.lower():
            continue

        lean_decls.append(
            {
                "lean_name": r.name,
                "decl_type": r.decl_type,
                "module_name": r.module_name,
                "statement_text": r.statement,
                "source_file": r.source_file,
                "docstring": r.docstring,
                "informal_description": r.informal_description,
            }
        )

        if len(lean_decls) >= limit:
            break

    return lean_decls


def format_result_for_prompt(result: LeanExploreResult) -> str:
    """Format a search result for inclusion in an LLM prompt."""
    parts = [f"**{result.name}**"]

    if result.informal_description:
        parts.append(f"  Description: {result.informal_description}")
    elif result.docstring:
        doc = (
            result.docstring[:200] + "..."
            if len(result.docstring) > 200
            else result.docstring
        )
        parts.append(f"  Doc: {doc}")

    statement = result.statement
    if len(statement) > 300:
        statement = statement[:300] + "..."
    parts.append("\n".join(f"  {line}" for line in lean_block(statement).splitlines()))

    parts.append(f"  Source: {result.source_file}")

    return "\n".join(parts)


def format_results_for_prompt(
    results: List[LeanExploreResult], max_results: int = 8
) -> str:
    """Format multiple search results for inclusion in an LLM prompt."""
    if not results:
        return "No relevant theorems found."

    formatted = []
    for i, result in enumerate(results[:max_results], 1):
        formatted.append(f"{i}. {format_result_for_prompt(result)}")

    return "\n\n".join(formatted)


async def get_semantic_hints(
    informal_reasoning: str,
    results_per_section: int = 3,
    package_filters: Optional[List[str]] = None,
) -> str:
    """Get semantic search hints from LeanExplore based on informal reasoning.

    This first extracts lemma search suggestions from the informal reasoning,
    then searches for those specific suggestions plus general semantic sections.

    The informal reasoning is expected to contain a section starting with
    "Consider searching lemmas in Mathlib:" followed by lemma descriptions.

    Args:
        informal_reasoning: Informal reasoning text (markdown format)
        results_per_section: Number of results per section (default: 3)
        package_filters: Optional list of packages to search

    Returns:
        Formatted string of relevant lemmas for inclusion in prompts,
        or empty string if no results found or service disabled.
    """
    from utils.markdown_helpers import split_markdown_into_sections
    import re

    if package_filters is None:
        package_filters = list(DEFAULT_LEANEXPLORE_PACKAGES)

    try:
        all_results = []
        seen_names: set[str] = set()

        # Extract specific lemma search suggestions from informal reasoning
        search_suggestions = _extract_search_suggestions(informal_reasoning)

        if search_suggestions:
            logger.info(f"Found {len(search_suggestions)} specific lemma search suggestions")

            # Search for each extracted suggestion
            for i, suggestion in enumerate(search_suggestions, 1):
                if len(suggestion.strip()) < 10:  # Skip very short suggestions
                    continue

                logger.info(f"Searching suggestion {i}/{len(search_suggestions)}: {suggestion}")

                try:
                    results = await semantic_search(
                        query=suggestion,
                        num_results=results_per_section + 1,  # fetch a few extra for dedup
                        package_filters=package_filters,
                    )

                    # Take top K unique results from this suggestion
                    count = 0
                    for r in results:
                        if r.name not in seen_names:
                            seen_names.add(r.name)
                            all_results.append(r)
                            count += 1
                            if count >= results_per_section:
                                break

                    logger.info(f"  Found {count} unique results for suggestion {i}")

                except Exception as e:
                    logger.debug(f"Search failed for suggestion '{suggestion[:50]}...': {e}")
                    continue

            logger.info(f"Completed search for all {len(search_suggestions)} suggestions. Total results: {len(all_results)}")

        else:
            logger.info("No specific search suggestions found, falling back to section-based search")

            # Fallback: split reasoning into semantic sections for broader search
            sections = split_markdown_into_sections(informal_reasoning)
            logger.info(f"Split informal reasoning into {len(sections)} sections for broader search")

            for i, section in enumerate(sections):
                if len(section) < 20:  # Skip very short sections
                    continue

                try:
                    results = await semantic_search(
                        query=section,
                        num_results=results_per_section + 2,  # fetch a few extra for dedup
                        package_filters=package_filters,
                    )

                    # Take top K unique results from this section
                    count = 0
                    for r in results:
                        if r.name not in seen_names:
                            seen_names.add(r.name)
                            all_results.append(r)
                            count += 1
                            if count >= results_per_section:
                                break

                except Exception as e:
                    logger.debug(f"Search failed for section {i}: {e}")
                    continue

        if not all_results:
            logger.info("No semantic search results found")
            return ""

        logger.info(
            f"Found {len(all_results)} unique results total"
        )
        logger.info(f"Selected candidates: {[r.name for r in all_results]}")

        # Format for prompt
        formatted = format_results_for_prompt(all_results, max_results=len(all_results))
        return f"### Useful Lemmas\n\n{formatted}"

    except Exception as e:
        logger.warning(f"Semantic search failed: {e}")
        return ""


def _extract_search_suggestions(informal_reasoning: str) -> List[str]:
    """Extract lemma search suggestions from informal reasoning.

    Looks for the section "Consider searching lemmas in Mathlib:" and extracts
    the lemma descriptions that follow.

    Args:
        informal_reasoning: The informal reasoning text

    Returns:
        List of lemma description strings to search for
    """
    import re

    suggestions = []

    # Find the search suggestions section
    # Look for "Consider searching lemmas in Mathlib:" followed by items until next section
    pattern = r"Consider searching lemmas in Mathlib:\s*\n?(.*?)(?:\n\s*\*\*|\Z)"
    match = re.search(pattern, informal_reasoning, re.IGNORECASE | re.MULTILINE | re.DOTALL)

    if match:
        suggestions_text = match.group(1)

        # Extract individual suggestions (lines starting with a., b., etc.)
        # Handle possible indentation
        suggestion_lines = re.findall(r"\s*[a-z]\.\s*(.+)", suggestions_text, re.IGNORECASE)

        for suggestion in suggestion_lines:
            # Clean up the suggestion text
            cleaned = suggestion.strip()
            if cleaned and len(cleaned) > 5:  # Only keep non-trivial suggestions
                suggestions.append(cleaned)

    return suggestions
