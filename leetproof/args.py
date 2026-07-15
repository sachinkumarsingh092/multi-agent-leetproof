import argparse
import json
from enum import Enum
from pathlib import Path
from typing import Optional, Dict, Any
from datetime import datetime
from config.limits import Limits

from config.constants import SESSIONS_DIR

_parsed_args: Optional[argparse.Namespace] = None


def load_session_params(session_name: str) -> Optional[Dict[str, Any]]:
    """Load session parameters from JSON.

    Args:
        session_name: Session name to load params for

    Returns:
        Dict of session params, or None if not found
    """
    params_file = Path(SESSIONS_DIR) / session_name / "session_params.json"

    if not params_file.exists():
        return None

    try:
        with open(params_file) as f:
            return json.load(f)
    except (json.JSONDecodeError, IOError):
        return None


def save_session_params(
    session_name: str,
    provider: str,
    model: str,
    input_file: Optional[str] = None,
    output_file: Optional[str] = None,
    max_input_tokens: Optional[int] = None,
    max_output_tokens: Optional[int] = None,
    max_total_tokens: Optional[int] = None,
    max_cost: Optional[float] = None,
    agent_context: Optional[str] = None,
    prover_v2_max_iterations: Optional[int] = None,
) -> None:
    """Save session parameters to JSON for later resumption.

    Args:
        session_name: Session name (used as directory name)
        provider: LLM provider name
        model: LLM model name
        input_file: Input problem file path
        output_file: Output Lean file path
        max_input_tokens: Token limit for input tokens
        max_output_tokens: Token limit for output tokens
        max_total_tokens: Token limit for total tokens
        max_cost: Cost limit in USD
        agent_context: JSON string mapping agent names to context file paths
        prover_v2_max_iterations: Max tool-loop iterations for prover_v2
    """
    session_dir = Path(SESSIONS_DIR) / session_name
    session_dir.mkdir(parents=True, exist_ok=True)

    params = {
        "provider": provider,
        "model": model,
        "input_file": input_file,
        "output_file": output_file,
        "max_input_tokens": max_input_tokens,
        "max_output_tokens": max_output_tokens,
        "max_total_tokens": max_total_tokens,
        "max_cost": max_cost,
        "agent_context": agent_context,
        "prover_v2_max_iterations": prover_v2_max_iterations,
    }

    params_file = session_dir / "session_params.json"
    with open(params_file, "w") as f:
        json.dump(params, f, indent=2)


class Stage(str, Enum):
    """Pipeline stages for sequential execution."""

    SPECGEN = "specgen"  # Stage 1: Specification Generation (includes PBT)
    CODEGEN = "codegen"  # Stage 2: Code Generation
    INVGEN = "invgen"  # Stage 4: Invariant Generation
    VERIFY = "verify"  # Stage 5: Verification


def get_parser() -> argparse.ArgumentParser:
    """Get the argument parser with all configured arguments."""
    parser = argparse.ArgumentParser(description="LLoom Agent")

    # Project directory (required)
    parser.add_argument(
        "--project",
        type=str,
        required=True,
        help="Path to the Lean project directory (containing lakefile.lean). "
        "All state (.sessions, logs, DB) is stored here.",
    )

    # Model provider configuration
    parser.add_argument(
        "--provider",
        type=str,
        choices=["openai", "google", "anthropic", "ollama", "groq", "cerebras"],
        default=None,
        help="The model provider to use",
    )

    parser.add_argument(
        "--model",
        type=str,
        default=None,
        help="The specific model to use (provider-specific, uses default if not specified)",
    )

    # Specification for the program to generate (required unless using state-file)
    parser.add_argument(
        "--specification",
        "-s",
        type=str,
        default=None,
        help="The specification for the Velvet program to generate (required unless using --state-file)",
    )

    parser.add_argument(
        "--input-file",
        "-i",
        type=str,
        default=None,
        help="Input file path (for verification-only workflow)",
    )

    parser.add_argument(
        "--output-file",
        "-o",
        type=str,
        default=None,
        help="Output file path for the generated program",
    )

    # Pipeline stage selection
    parser.add_argument(
        "--start",
        type=str,
        choices=[s.value for s in Stage],
        default=Stage.SPECGEN.value,
        help="Pipeline stage to start from (default: specgen)",
    )

    parser.add_argument(
        "--end",
        type=str,
        choices=[s.value for s in Stage],
        default=None,
        help="Pipeline stage to end at (default: verify)",
    )

    parser.add_argument(
        "--recursion-limit",
        "-r",
        type=int,
        default=100,
        help="Maximum recursion depth for graph execution (default: 100)",
    )

    parser.add_argument(
        "--state-file",
        type=str,
        default=None,
        help="Path to JSON state file for standalone agent execution (optional)",
    )

    parser.add_argument(
        "--session-name",
        "-n",
        type=str,
        default=datetime.now().strftime("%Y-%m-%d_%H-%M-%S"),
        help="Session name for workflow identification and resumption (default: timestamp YYYY-MM-DD_HH-MM-SS)",
    )

    parser.add_argument(
        "--resume",
        action="store_true",
        default=False,
        help="Resume an existing workflow by session name. Requires --session-name.",
    )

    parser.add_argument(
        "--list-workflows",
        action="store_true",
        default=False,
        help="List all workflows in the database and exit.",
    )

    # Agent-specific context injection
    parser.add_argument(
        "--agent-context",
        type=str,
        default=None,
        help="JSON mapping of agent names to context file paths. Context is injected into system prompts. "
        'Example: \'{"velvet_programmer": "prompts/velvet_documentation.md", "velvet_invariant_inferrer": "prompts/velvet_documentation.md"}\'',
    )

    parser.add_argument(
        "--agent-type",
        type=str,
        default=None,
        help="Type/name of the agent being judged (e.g., 'programmer', 'invariant_inferrer'). Used when running judge standalone.",
    )

    # Graph visualization
    parser.add_argument(
        "--print-graph",
        action="store_true",
        help="Print ASCII visualization of the workflow graph and exit",
    )

    # Logging configuration
    parser.add_argument(
        "--log-level",
        type=str,
        choices=["DEBUG", "INFO", "WARNING", "ERROR", "CRITICAL"],
        default="INFO",
        help="Console logging level (default: INFO). File logging always uses DEBUG.",
    )

    # Token limits (cutoff when exceeded)
    parser.add_argument(
        "--max-input-tokens",
        type=int,
        default=None,
        help="Maximum cumulative input/prompt tokens before stopping execution (default: unlimited)",
    )

    parser.add_argument(
        "--max-output-tokens",
        type=int,
        default=None,
        help="Maximum cumulative output/completion tokens before stopping execution (default: unlimited)",
    )

    parser.add_argument(
        "--max-total-tokens",
        type=int,
        default=None,
        help="Maximum cumulative total tokens before stopping execution (default: unlimited)",
    )

    parser.add_argument(
        "--max-cost",
        type=float,
        default=None,
        help="Maximum cost in USD before stopping execution (default: unlimited)",
    )

    # Spec PBT: property-based testing of spec during specgen loop (on by default)
    parser.add_argument(
        "--disable-spec-pbt",
        action="store_true",
        default=False,
        help="Disable property-based testing of the specification inside the specgen loop. "
             "By default PBT runs after each typechecked spec; if it finds a bug the spec is "
             "rejected and regenerated without calling the coach.",
    )

    parser.add_argument(
        "--prover-v2-max-iterations",
        type=int,
        default=None,
        help="Maximum tool-loop iterations for prover_v2 (default: 20)",
    )
    # TUI mode (enabled by default)
    parser.add_argument(
        "--no-tui",
        action="store_true",
        default=False,
        help="Disable Terminal UI mode, use plain log output instead",
    )

    return parser


def merge_session_params(args: argparse.Namespace) -> None:
    """Load saved session params and merge into args (CLI args take priority).

    Call this after os.chdir() to the project directory so that the relative
    ``.sessions/`` path resolves correctly.
    """
    if not (args.resume and args.session_name):
        return
    saved_params = load_session_params(args.session_name)
    if not saved_params:
        return
    if not args.provider:
        args.provider = saved_params.get("provider")
    if not args.model:
        args.model = saved_params.get("model")
    if not args.input_file:
        args.input_file = saved_params.get("input_file")
    if not args.output_file:
        args.output_file = saved_params.get("output_file")
    if args.max_input_tokens is None:
        args.max_input_tokens = saved_params.get("max_input_tokens")
    if args.max_output_tokens is None:
        args.max_output_tokens = saved_params.get("max_output_tokens")
    if args.max_total_tokens is None:
        args.max_total_tokens = saved_params.get("max_total_tokens")
    if args.max_cost is None:
        args.max_cost = saved_params.get("max_cost")
    if not args.agent_context:
        args.agent_context = saved_params.get("agent_context")
    if args.prover_v2_max_iterations is None:
        args.prover_v2_max_iterations = saved_params.get("prover_v2_max_iterations")


def parse_args() -> argparse.Namespace:
    """Parse command line arguments. Returns cached result if already parsed.

    Note: Does not validate required fields - each main file validates what it needs.
    Note: Call merge_session_params(args) after chdir to the project directory
    to load saved session params on resume.
    """
    global _parsed_args
    if _parsed_args is None:
        parser = get_parser()
        _parsed_args = parser.parse_args()

    return _parsed_args


def get_args() -> argparse.Namespace:
    """Get parsed arguments. Alias for parse_args()."""
    return parse_args()


def set_session_name(session_name: str) -> None:
    """Override the session name in the parsed arguments.

    This allows programmatic setting of the session name after parsing.
    """
    args = parse_args()
    args.session_name = session_name


def get_spec_parser() -> argparse.ArgumentParser:
    """Get the argument parser for spec generation workflows.

    This is an alias for get_parser() for backwards compatibility.
    """
    return get_parser()
