"""Tools specifically designed for SpecGen agent.

SpecGen has minimal tool access by design:
1. write_file - Write access to the target specification file (restricted via set_allowed_output_files)
2. lean_build_with_validation - Build with strict validation (no axioms, exactly one 'prove_correct FuncName by sorry' required)
3. lean_search (via MCP) - Search Lean libraries for relevant definitions
"""

import re
import subprocess
from pathlib import Path
from typing import Optional
from langchain_core.tools import tool

from logging_config import get_logger
from tools.mcp_tools import MCPToolsManager
from utils.lean.build import find_project_root
from tools.common import write_file, set_allowed_output_files

logger = get_logger(__name__)


def lean_build_with_validation_helper(file_path: str) -> dict:
    """Build and validate the Lean file with strict rules for SpecGen.

    VALIDATION RULES:
    1. NO axioms allowed (axioms bypass proof requirements)
    2. Exactly ONE 'prove_correct FuncName by sorry' statement required
    3. NO other sorry statements allowed besides the prove_correct one
    4. NO compilation errors allowed

    Args:
        file_path: Path to the Lean file to build

    Returns:
        Dictionary with keys:
        - typechecks: bool (True if all validation passed)
        - build_log: str (detailed build and validation output)
        - has_axiom: bool (whether axioms were detected)
        - sorry_count: int (number of sorry statements found)
    """
    try:
        # Get the Lean project root directory (where lakefile.lean/lakefile.toml is located)
        lean_root = Path(find_project_root(file_path))

        file_path_abs = Path(file_path).resolve()
        try:
            file_path_rel = file_path_abs.relative_to(lean_root)
        except ValueError:
            # If file is not under lean_root, use absolute path
            logger.warning(f"File {file_path} is not under Lean project root {lean_root}, using absolute path")
            file_path_rel = file_path_abs

        logger.info(f"lake build {file_path_rel}")
        # Lazy import to avoid circular dependency
        from config.timeouts import Timeouts
        result = subprocess.run(
            ["lake", "build", str(file_path_rel)],
            capture_output=True,
            text=True,
            timeout=Timeouts.LEAN_BUILD,
            cwd=str(lean_root)
        )

        output = result.stdout or ""
        errors = result.stderr or ""
        combined_output = f"{output}\n{errors}".strip()

        # Check for compilation errors (return code != 0)
        if result.returncode != 0:
            from logging_config import log_with_truncation
            import logging

            # Special handling for return code 137 (OOM killed)
            if result.returncode == 137:
                logger.error("=" * 80)
                logger.error("❌ PROCESS KILLED BY OOM (Out of Memory) - Return code 137")
                logger.error("=" * 80)
                logger.error(f"File: {file_path}")
                logger.error("")
                logger.error("The Lean build process was terminated by the system's OOM killer.")
                logger.error("This typically happens when:")
                logger.error("  - The system runs out of available RAM")
                logger.error("  - Lean compilation requires more memory than available")
                logger.error("  - Multiple memory-intensive processes are running")
                logger.error("")
                logger.error("Solutions:")
                logger.error("  1. Close other memory-intensive applications")
                logger.error("  2. Disable LeanExplore: export DISABLE_LEAN_EXPLORE=1")
                logger.error("  3. Disable embeddings: export DISABLE_RAG_EMBEDDINGS=1")
                logger.error("  4. Increase system RAM or swap space")
                logger.error("  5. Simplify the Lean specification")
                logger.error("")
                logger.error("Check system memory:")
                logger.error("  free -h    # On Linux")
                logger.error("  dmesg | grep -i 'killed process'    # Check OOM killer logs")
                logger.error("=" * 80)

                return {
                    "typechecks": False,
                    "build_log": f"PROCESS KILLED BY OOM (Return code 137)\n\nThe Lean build process was terminated by the system's OOM killer due to insufficient memory.\n\nSolutions:\n1. Close other applications\n2. Disable LeanExplore (export DISABLE_LEAN_EXPLORE=1)\n3. Disable embeddings (export DISABLE_RAG_EMBEDDINGS=1)\n4. Increase RAM or swap\n\nPartial output:\n{combined_output}",
                    "has_axiom": False,
                    "sorry_count": 0
                }

            # Special handling for negative return codes (killed by signal)
            if result.returncode < 0:
                signal_num = -result.returncode
                logger.error("=" * 80)
                logger.error(f"❌ PROCESS KILLED BY SIGNAL {signal_num}")
                logger.error("=" * 80)
                logger.error(f"File: {file_path}")
                logger.error(f"Signal: {signal_num}")
                logger.error("")
                if signal_num == 9:
                    logger.error("Signal 9 (SIGKILL) - Process was forcibly terminated")
                    logger.error("This may be due to OOM killer or manual kill -9")
                elif signal_num == 15:
                    logger.error("Signal 15 (SIGTERM) - Process was terminated")
                elif signal_num == 11:
                    logger.error("Signal 11 (SIGSEGV) - Segmentation fault")
                    logger.error("This indicates a crash in Lean or its dependencies")
                logger.error("=" * 80)

                return {
                    "typechecks": False,
                    "build_log": f"PROCESS KILLED BY SIGNAL {signal_num}\n\nPartial output:\n{combined_output}",
                    "has_axiom": False,
                    "sorry_count": 0
                }

            # Normal compilation errors
            logger.error("=" * 80)
            logger.error("❌ BUILD FAILED - Lean compilation errors detected")
            logger.error("=" * 80)
            logger.error(f"Return code: {result.returncode}")
            logger.error(f"File: {file_path}")
            logger.error("")
            logger.error("Build output (stdout):")
            logger.error("-" * 80)
            if output:
                # Log first 2000 chars to console, full to file
                log_with_truncation(logger, logging.ERROR, output, console_max_length=2000)
            else:
                logger.error("(no stdout output)")
            logger.error("-" * 80)
            logger.error("")
            logger.error("Build errors (stderr):")
            logger.error("-" * 80)
            if errors:
                log_with_truncation(logger, logging.ERROR, errors, console_max_length=2000)
            else:
                logger.error("(no stderr output)")
            logger.error("-" * 80)
            logger.error("=" * 80)

            return {
                "typechecks": False,
                "build_log": f"BUILD FAILED with errors:\n{combined_output}",
                "has_axiom": False,
                "sorry_count": 0
            }

        # Read the source file to check for sorry patterns
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                source_content = f.read()
        except Exception as e:
            logger.warning(f"Could not read source file for sorry validation: {e}")
            source_content = ""

        # Count all 'sorry' occurrences in source (case-insensitive)
        total_sorry_count = len(re.findall(r'\bsorry\b', source_content, re.IGNORECASE))

        # Count 'prove_correct ... by sorry' patterns
        # Pattern: prove_correct <FuncName> by sorry
        prove_correct_sorry_pattern = r'\bprove_correct\s+\w+\s+by\s+sorry\b'
        prove_correct_sorry_count = len(re.findall(prove_correct_sorry_pattern, source_content, re.IGNORECASE))

        # Check for axioms
        has_axiom = bool(re.search(r'\baxiom\b', combined_output, re.IGNORECASE))

        # Validation checks
        validation_errors = []

        if has_axiom:
            validation_errors.append("❌ AXIOMS DETECTED - Axioms are not allowed in specifications")

        # Refined sorry validation:
        # - Should have exactly 1 'prove_correct FuncName by sorry'
        # - Should have no other sorry besides the one in prove_correct
        if total_sorry_count == 0:
            validation_errors.append("❌ MISSING PROVE_CORRECT - Expected 'prove_correct FuncName by sorry' statement")
        elif total_sorry_count == 1:
            # One sorry is allowed, but it must be in the prove_correct statement
            if prove_correct_sorry_count != 1:
                validation_errors.append(
                    "❌ INVALID SORRY - Found 1 'sorry' but it's not in the required 'prove_correct FuncName by sorry' format"
                )
        else:
            # Multiple sorries detected
            extra_sorry_count = total_sorry_count - prove_correct_sorry_count
            if prove_correct_sorry_count == 0:
                validation_errors.append(
                    f"❌ TOO MANY SORRIES - Found {total_sorry_count} 'sorry' statement(s), "
                    f"but none in 'prove_correct FuncName by sorry' format. "
                    f"Only one sorry is allowed, and it must be in the prove_correct statement."
                )
            elif prove_correct_sorry_count == 1:
                validation_errors.append(
                    f"❌ TOO MANY SORRIES - Found {total_sorry_count} 'sorry' statement(s) "
                    f"({extra_sorry_count} extra besides the prove_correct). "
                    f"Only one sorry is allowed, in 'prove_correct FuncName by sorry' format."
                )
            else:
                validation_errors.append(
                    f"❌ TOO MANY SORRIES - Found {total_sorry_count} 'sorry' statement(s) "
                    f"with {prove_correct_sorry_count} in prove_correct statements. "
                    f"Only one sorry is allowed, in 'prove_correct FuncName by sorry' format."
                )

        if validation_errors:
            error_summary = "\n".join(validation_errors)
            logger.error(f"Validation failed:\n{error_summary}")
            return {
                "typechecks": False,
                "build_log": f"BUILD SUCCESSFUL but VALIDATION FAILED:\n\n{error_summary}\n\nBuild output:\n{combined_output}",
                "has_axiom": has_axiom,
                "sorry_count": total_sorry_count
            }

        # All checks passed
        logger.info("✓ Build successful with valid specification (exactly one 'prove_correct FuncName by sorry', no axioms, no errors)")
        return {
            "typechecks": True,
            "build_log": f"✓ BUILD AND VALIDATION SUCCESSFUL\n- Exactly one 'prove_correct FuncName by sorry' statement\n- No axioms\n- No errors\n\nBuild output:\n{combined_output}",
            "has_axiom": False,
            "sorry_count": total_sorry_count
        }

    except subprocess.TimeoutExpired:
        error_msg = "Build timed out after 120 seconds"
        logger.error(error_msg)
        return {
            "typechecks": False,
            "build_log": error_msg,
            "has_axiom": False,
            "sorry_count": 0
        }
    except Exception as e:
        error_msg = f"Build error: {str(e)}"
        logger.error(error_msg)
        return {
            "typechecks": False,
            "build_log": error_msg,
            "has_axiom": False,
            "sorry_count": 0
        }


@tool
def lean_build_with_validation(file_path: str) -> str:
    """Build and validate the Lean file with strict rules for SpecGen.

    VALIDATION RULES:
    1. NO axioms allowed (axioms bypass proof requirements)
    2. Exactly ONE 'prove_correct FuncName by sorry' statement required
    3. NO other sorry statements allowed besides the prove_correct one
    4. NO compilation errors allowed

    This tool validates that your specification is well-formed.

    Args:
        file_path: Path to the Lean file to build

    Returns:
        Build output with validation results (human-readable string)
    """
    result = lean_build_with_validation_helper(file_path)
    return result["build_log"]


# Global MCP manager for SpecGen tools
_spec_gen_mcp_manager: Optional[MCPToolsManager] = None
_spec_gen_cached_tools: Optional[list] = None


async def get_lean_search_tools() -> list:
    """Get LeanSearch tools for finding Lean library definitions.

    This uses the LeanSearch MCP server which provides:
    - Natural language search for Lean definitions
    - Library theorem lookup
    - Type-based search

    Returns:
        List of LeanSearch tools
    """
    global _spec_gen_mcp_manager

    if _spec_gen_mcp_manager is None:
        _spec_gen_mcp_manager = MCPToolsManager()

        # LeanSearch MCP server configuration
        # Install: npm install -g leansearch-mcp
        mcp_servers = {
            # "leanexploreAPI": {
            #     "command": "leanexplore",
            #     "args": [
            #         "mcp",
            #         "serve",
            #         "--backend",
            #         "api",
            #     ]
            # }
        }

        try:
            await _spec_gen_mcp_manager.initialize(mcp_servers)
            logger.info("✓ Initialized LeanSearch MCP tools for SpecGen")
        except Exception as e:
            logger.warning(f"Failed to initialize LeanSearch MCP: {e}")
            logger.info("SpecGen will continue without LeanSearch tools")
            return []

    return _spec_gen_mcp_manager.get_tools()


async def get_spec_gen_tools() -> list:
    """Get all tools available to SpecGen agent.

    SpecGen has minimal, focused tools:
    1. write_file - Write the specification file (restricted via set_allowed_output_files)
    2. LeanSearch tools (via MCP) - Search Lean libraries for relevant definitions

    SpecGen does NOT have:
    - Build/typecheck tools (compilation is done by main workflow after generation)
    - Read/list file tools (all context is provided in the prompt)

    This minimal design ensures SpecGen focuses on generation while being able
    to search for relevant Lean library functions when needed.

    NOTE: Before calling this, must call set_allowed_output_files([output_file])
          to restrict write_file to only the target specification file.

    Returns:
        List of tools for SpecGen
    """
    global _spec_gen_cached_tools

    if _spec_gen_cached_tools is None:
        logger.info("Loading SpecGen tools...")

        # Core tool - write only (restriction set via set_allowed_output_files)
        core_tools = [
            write_file
        ]

        # Add LeanSearch tools
        try:
            lean_search_tools = await get_lean_search_tools()
            _spec_gen_cached_tools = core_tools + lean_search_tools
            logger.info(f"✓ Loaded {len(_spec_gen_cached_tools)} SpecGen tools: "
                       f"{[t.name for t in _spec_gen_cached_tools]}")
        except Exception as e:
            logger.warning(f"Could not load LeanSearch tools: {e}")
            _spec_gen_cached_tools = core_tools
            logger.info(f"✓ Loaded {len(_spec_gen_cached_tools)} SpecGen tools (without LeanSearch)")

    return _spec_gen_cached_tools


async def cleanup_spec_gen_mcp():
    """Cleanup SpecGen MCP connections."""
    global _spec_gen_mcp_manager, _spec_gen_cached_tools
    if _spec_gen_mcp_manager:
        await _spec_gen_mcp_manager.cleanup()
        _spec_gen_mcp_manager = None
        _spec_gen_cached_tools = None
        logger.info("✓ Cleaned up SpecGen MCP connections")


# For backward compatibility and convenience
SPEC_GEN_TOOLS = []  # Will be populated by get_spec_gen_tools()
