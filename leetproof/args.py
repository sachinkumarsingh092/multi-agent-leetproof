import argparse
import json
from enum import Enum
from pathlib import Path
from typing import Optional, Dict, Any
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
    start: Optional[str] = None,
    end: Optional[str] = None,
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
        start: First pipeline stage
        end: Last pipeline stage
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
        "start": start,
        "end": end,
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

    SPECGEN = "specgen"
    CODEGEN = "codegen"
    INVGEN = "invgen"
    VERIFY = "verify"


def get_parser() -> argparse.ArgumentParser:
    """Get the argument parser with all configured arguments."""
    parser = argparse.ArgumentParser(description="LLoom Agent")

    # Project directory
    parser.add_argument(
        "--project",
        type=str,
        default=".",
        help="Path to the Lean project directory (containing lakefile.toml or "
        "lakefile.lean). Defaults to the current directory. All worker state "
        "is stored under its .lloom directory.",
    )

    # Model provider configuration
    parser.add_argument(
        "--provider",
        type=str,
        choices=["openai", "google", "anthropic"],
        default=None,
        help="The model provider to use",
    )

    parser.add_argument(
        "--model",
        type=str,
        default=None,
        help="The specific model to use (provider-specific, uses default if not specified)",
    )

    parser.add_argument(
        "--input-file",
        "-i",
        type=str,
        default=None,
        help="Reviewed .txt specification for specgen, or a .lean file for later stages",
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
        help=argparse.SUPPRESS,
    )

    parser.add_argument(
        "--session-name",
        "-n",
        type=str,
        default=None,
        help="Unique job/session identifier used for artifacts and resumption. "
        "Pipeline runs generate one automatically when omitted.",
    )

    parser.add_argument(
        "--resume",
        action="store_true",
        default=False,
        help="Resume an existing workflow by session name. Requires --session-name.",
    )

    # Agent-specific context injection
    parser.add_argument(
        "--agent-context",
        type=str,
        default=None,
        help="JSON mapping of agent names to context file paths. Context is injected into system prompts. "
        'Example: \'{"velvet_programmer": "prompts/velvet_documentation.md", "velvet_invariant_inferrer": "prompts/velvet_documentation.md"}\'',
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

    parser.add_argument(
        "--prover-v2-max-iterations",
        type=int,
        default=None,
        help="Maximum tool-loop iterations for prover_v2 (default: 20)",
    )

    return parser


def merge_session_params(args: argparse.Namespace) -> None:
    """Load saved session params and merge into args (CLI args take priority).

    Call this after os.chdir() to the project directory so that the relative
    ``.lloom/sessions/`` path resolves correctly.
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
    if saved_params.get("start"):
        args.start = saved_params["start"]
    if "end" in saved_params:
        args.end = saved_params["end"]
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
