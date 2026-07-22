"""CLI entry point for the lloom-agent binary."""

import argparse
import json
import os
import sys

SUBCOMMANDS = {
    "prepare":    "Expand a short request into a reviewable text specification",
    "pipeline":   "Formalize a reviewed specification, then generate and verify code",
    "setup":      "Check Lean and download theorem-search assets",
    "search":     "Semantic theorem search (LeanExplore)",
    "query":      "Run analytics SQL or a typed analytics query operation and print JSON",
    "lean-synth": "Standalone Lean synthesis + verification",
    "prove-from-file": "Prove sorry'd goals in a Lean file using ProverV2",
    "get-sorried-files": "Find sorried goals in Lean files",
    "workflows":  "Inspect DBOS workflows stored in the project SQLite DBs",
}


def _rewrite_argv(subcommand: str):
    """Strip the subcommand from argv and set prog name for --help."""
    sys.argv = ["lloom-agent " + subcommand] + sys.argv[2:]


def print_help():
    print("Usage: lloom-agent <command> [args...]\n")
    print("Commands:")
    pad = max(len(k) for k in SUBCOMMANDS) + 2
    for cmd, desc in SUBCOMMANDS.items():
        print(f"  {cmd:<{pad}} {desc}")
    print(f"\n  If no command is given, 'pipeline' is assumed.")
    print(f"\nRun 'lloom-agent <command> --help' for command-specific options.")


def run_setup():
    """Check Lean and download theorem-search assets."""
    import subprocess

    print("=" * 60)
    print("LLoom Setup")
    print("=" * 60)
    failures = []

    # 1. Check lean/lake
    print("\n1. Checking Lean toolchain...")
    try:
        result = subprocess.run(["lean", "--version"], capture_output=True, text=True, timeout=10)
        if result.returncode == 0:
            print(f"   OK: {result.stdout.strip().splitlines()[0]}")
        else:
            print("   WARN: lean found but returned an error")
    except FileNotFoundError:
        print("   MISSING: lean not found in PATH")
        print("   Install elan: curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh")
        failures.append("lean")
    except subprocess.TimeoutExpired:
        print("   ERROR: lean --version timed out (may be downloading toolchain)")
        failures.append("lean")
    except Exception as e:
        print(f"   ERROR: lean check failed: {e}")
        failures.append("lean")

    # 2. Setup LeanExplore
    print("\n2. Setting up LeanExplore (semantic search, ~8GB download)...")
    try:
        from lean_explore.cli.data_commands import fetch
        fetch()
        print("   OK: LeanExplore data ready")
    except SystemExit:
        print("   OK: LeanExplore data ready")
    except Exception as e:
        print(f"   FAIL: {e}")
        failures.append("leanexplore")

    # 3. Cache the embedding model required by LeanExplore.
    print("\n3. Caching LeanExplore embedding model (~400MB)...")
    try:
        from sentence_transformers import SentenceTransformer

        model = SentenceTransformer("BAAI/bge-base-en-v1.5", device="cpu")
        model.encode(["worker setup check"])
        del model
        print("   OK: embedding model cached")
    except Exception as e:
        print(f"   FAIL: {e}")
        failures.append("embedding-model")

    # Summary
    print("\n" + "=" * 60)
    if not failures:
        print("Setup complete! All components ready.")
    else:
        print(f"Setup completed with {len(failures)} failure(s): {', '.join(failures)}")
        print("Fix the issues above and re-run: lloom-agent setup")
        sys.exit(1)


def run_query():
    """Execute an analytics SQL query or typed analytics query operation."""
    parser = argparse.ArgumentParser(
        prog="lloom-agent query",
        description=(
            "Run a read-only SQL query or invoke a typed analytics query operation and print JSON."
        ),
    )
    parser.add_argument(
        "--project",
        type=str,
        required=True,
        help="Path to the project directory containing .lloom/db/analytics.sqlite",
    )
    parser.add_argument(
        "--operation",
        type=str,
        help=(
            "Typed analytics query operation to invoke, e.g. "
            "'velvet_programmer.query_typecheck_summaries'"
        ),
    )
    parser.add_argument(
        "--input",
        type=str,
        help="JSON object passed as keyword arguments to --operation",
    )
    parser.add_argument(
        "--list-operations",
        action="store_true",
        help="List available typed analytics query operations as JSON",
    )
    parser.add_argument(
        "sql",
        nargs="?",
        type=str,
        help="Read-only SQL query (SELECT/WITH only)",
    )
    args = parser.parse_args(sys.argv[2:])

    if args.list_operations and (args.operation or args.input or args.sql):
        parser.error("--list-operations cannot be combined with --operation, --input, or SQL")
    if args.input and not args.operation:
        parser.error("--input requires --operation")
    if args.operation and args.sql:
        parser.error("Provide either SQL or --operation, not both")
    if not args.list_operations and not args.operation and not args.sql:
        parser.error("Provide either SQL or --operation")

    project_dir = os.path.abspath(args.project)
    if not os.path.isdir(project_dir):
        print(f"Error: --project directory does not exist: {project_dir}", file=sys.stderr)
        sys.exit(1)

    os.chdir(project_dir)

    from utils.analytics.common import to_json_value
    from utils.analytics.query import (
        execute_query_operation,
        list_query_operations,
        query as query_analytics,
    )

    try:
        if args.list_operations:
            result = list_query_operations()
        elif args.operation:
            input_data: object = {}
            if args.input:
                input_data = json.loads(args.input)
                if not isinstance(input_data, dict):
                    raise ValueError("--input must decode to a JSON object")
            result = execute_query_operation(args.operation, input_data)
        else:
            result = query_analytics(args.sql)
    except Exception as e:
        print(f"Error: analytics query failed: {e}", file=sys.stderr)
        sys.exit(1)

    print(json.dumps(to_json_value(result), indent=2, ensure_ascii=False))


def _render_step_state(step) -> str:
    if step.error is not None:
        return "ERROR"
    if step.child_workflow_id:
        return f"CHILD:{step.child_status or 'UNKNOWN'}"
    if step.completed_at_epoch_ms is not None:
        return "DONE"
    return "PENDING"


def run_workflows():
    """Inspect DBOS workflows stored in SQLite."""

    common = argparse.ArgumentParser(add_help=False)
    common.add_argument(
        "--project",
        type=str,
        required=True,
        help="Path to the project directory containing .lloom/db/",
    )
    common.add_argument(
        "--db",
        action="append",
        default=[],
        help=(
            "Workflow DB selector. Can be repeated. Accepts a short DB name like "
            "'pipeline', a filename like 'lloom_pipeline.sqlite', or a full path."
        ),
    )
    common.add_argument(
        "--json",
        action="store_true",
        help="Print machine-readable JSON instead of formatted text.",
    )

    parser = argparse.ArgumentParser(
        prog="lloom-agent workflows",
        description="Inspect DBOS workflows and steps stored in .lloom/db/*.sqlite",
    )
    subparsers = parser.add_subparsers(dest="operation", required=True)

    list_parser = subparsers.add_parser("list", help="List workflows", parents=[common])
    list_parser.add_argument(
        "--regex",
        type=str,
        help="Python regex applied to workflow id, status, name, class, config, and fork source.",
    )
    list_parser.add_argument(
        "--status",
        type=str,
        help="Filter by exact workflow status (for example PENDING, SUCCESS, ERROR).",
    )
    list_parser.add_argument(
        "--limit",
        type=int,
        default=100,
        help="Maximum number of workflows to print (default: 100).",
    )

    show_parser = subparsers.add_parser("show", help="Show one workflow and its steps", parents=[common])
    show_parser.add_argument("workflow_id", type=str, help="Exact workflow id")
    show_parser.add_argument(
        "--full",
        action="store_true",
        help="Print full workflow payloads instead of truncating them.",
    )

    step_parser = subparsers.add_parser("step", help="Show one workflow step", parents=[common])
    step_parser.add_argument("workflow_id", type=str, help="Exact workflow id")
    step_parser.add_argument("step_id", type=int, help="Step/function id")
    step_parser.add_argument(
        "--full",
        action="store_true",
        help="Print full step payloads instead of truncating them.",
    )

    args = parser.parse_args(sys.argv[2:])

    project_dir = os.path.abspath(args.project)
    if not os.path.isdir(project_dir):
        print(f"Error: --project directory does not exist: {project_dir}", file=sys.stderr)
        sys.exit(1)

    from utils.dbos_inspect import (
        format_payload,
        format_timestamp,
        get_step_detail,
        get_workflow_detail,
        list_workflows,
        to_dict,
    )

    selectors = args.db or None
    try:
        if args.operation == "list":
            workflows = list_workflows(
                project_dir,
                selectors=selectors,
                regex=args.regex,
                status=args.status,
                limit=args.limit,
            )
            if args.json:
                print(json.dumps(to_dict(workflows), indent=2, ensure_ascii=False))
                return
            if not workflows:
                print("No workflows found.")
                return

            db_width = max(len("DB"), max(len(wf.db_name) for wf in workflows))
            status_width = max(len("STATUS"), max(len(wf.status or "-") for wf in workflows))
            print(
                f"{'DB':<{db_width}}  {'STATUS':<{status_width}}  {'CREATED':<20}  WORKFLOW ID"
            )
            for wf in workflows:
                print(
                    f"{wf.db_name:<{db_width}}  "
                    f"{(wf.status or '-'):<{status_width}}  "
                    f"{format_timestamp(wf.created_at_ms):<20}  "
                    f"{wf.workflow_uuid}"
                )
            return

        if args.operation == "show":
            detail = get_workflow_detail(project_dir, args.workflow_id, selectors=selectors)
            if args.json:
                print(json.dumps(to_dict(detail), indent=2, ensure_ascii=False, default=str))
                return

            summary = detail.summary
            print(f"Workflow: {summary.workflow_uuid}")
            print(f"DB: {summary.db_name}")
            print(f"Status: {summary.status or '-'}")
            print(f"Name: {summary.name or '-'}")
            print(f"Class: {summary.class_name or '-'}")
            print(f"Config: {summary.config_name or '-'}")
            print(f"Created: {format_timestamp(summary.created_at_ms)}")
            print(f"Updated: {format_timestamp(summary.updated_at_ms)}")
            print(f"Recovery Attempts: {summary.recovery_attempts if summary.recovery_attempts is not None else '-'}")
            print(f"Forked From: {summary.forked_from or '-'}")
            print(f"Executor: {summary.executor_id or '-'}")
            print(f"Queue: {summary.queue_name or '-'}")

            print("\nWorkflow Inputs:")
            print(format_payload(detail.inputs, full=args.full))
            print("\nWorkflow Output:")
            print(format_payload(detail.output, full=args.full))
            print("\nWorkflow Error:")
            print(format_payload(detail.error, full=args.full))

            print("\nSteps:")
            if not detail.steps:
                print("  <none>")
                return
            print(f"{'ID':>4}  {'STATE':<16}  {'STARTED':<20}  {'CHILD WORKFLOW':<44}  FUNCTION")
            for step in detail.steps:
                child = step.child_workflow_id or "-"
                if step.child_workflow_id and step.child_status:
                    child = f"{step.child_workflow_id} ({step.child_status})"
                print(
                    f"{step.function_id:>4}  "
                    f"{_render_step_state(step):<16}  "
                    f"{format_timestamp(step.started_at_epoch_ms):<20}  "
                    f"{child:<44}  "
                    f"{step.function_name}"
                )
            return

        if args.operation == "step":
            detail = get_step_detail(
                project_dir,
                args.workflow_id,
                args.step_id,
                selectors=selectors,
            )
            if args.json:
                print(json.dumps(to_dict(detail), indent=2, ensure_ascii=False, default=str))
                return

            print(f"Workflow: {detail.workflow_uuid}")
            print(f"DB: {detail.db_name}")
            print(f"Step ID: {detail.function_id}")
            print(f"Function: {detail.function_name}")
            print(f"Started: {format_timestamp(detail.started_at_epoch_ms)}")
            print(f"Completed: {format_timestamp(detail.completed_at_epoch_ms)}")
            print(f"Child Workflow: {detail.child_workflow_id or '-'}")
            print(f"Child Status: {detail.child_status or '-'}")
            print("Step Input: <not available in operation_outputs schema>")
            print("\nStep Output:")
            print(format_payload(detail.output, full=args.full))
            print("\nStep Error:")
            print(format_payload(detail.error, full=args.full))
            return
    except Exception as e:
        print(f"Error: workflow inspection failed: {e}", file=sys.stderr)
        sys.exit(1)


def main():
    if len(sys.argv) > 1:
        cmd = sys.argv[1]

        if cmd in ("--help", "-h", "help"):
            print_help()
            return

        if cmd == "setup":
            if len(sys.argv) > 2 and sys.argv[2] in ("--help", "-h"):
                print("Usage: lloom-agent setup\n")
                print("Check Lean and download LeanExplore search assets.")
                return
            run_setup()
            sys.exit(0)
        elif cmd == "prepare":
            _rewrite_argv("prepare")
            from prepare import main as prepare_main
            prepare_main()
            return
        elif cmd == "search":
            import asyncio
            _rewrite_argv("search")
            from scripts.lean_explore_cli import main as search_main
            asyncio.run(search_main())
            return
        elif cmd == "query":
            run_query()
            return
        elif cmd == "lean-synth":
            _rewrite_argv("lean-synth")
            from agents.lean_synth_and_verify import main as lean_synth_main
            lean_synth_main()
            return
        elif cmd == "prove-from-file":
            _rewrite_argv("prove-from-file")
            from prove_from_file import main as prove_from_file_main
            prove_from_file_main()
            return
        elif cmd == "get-sorried-files":
            _rewrite_argv("get-sorried-files")
            from scripts.get_sorried_files import main as get_sorried_files_main
            get_sorried_files_main()
            return
        elif cmd == "workflows":
            run_workflows()
            return
        elif cmd == "pipeline":
            _rewrite_argv("pipeline")

    # Default: pipeline (also handles bare `lloom-agent` with no args,
    # which will show pipeline's own --help via argparse)
    if len(sys.argv) <= 1 or sys.argv[1] not in SUBCOMMANDS:
        sys.argv[0] = "lloom-agent pipeline"
    from pipeline import main as pipeline_main
    pipeline_main()


if __name__ == "__main__":
    main()
