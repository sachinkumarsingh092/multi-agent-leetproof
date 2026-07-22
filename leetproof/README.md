# LeetProof Python worker

This package implements LeetProof's natural-language preparation and verified
implementation worker.

## Core commands

`prepare.py` expands a short request into a detailed natural-language
specification for human review:

```bash
uv run lloom-agent prepare \
  "Return the larger of two natural numbers" \
  --output-file <specification.txt> \
  --provider <openai|google|anthropic> \
  --model <model>
```

The command opens an editor containing `TASK_DESCRIPTION`, `METHOD_SIGNATURE`,
and JSON `TEST_CASES` sections. `Ctrl+R` opens a feedback dialog for model
revision, `Ctrl+S` validates and saves the approved `.txt`, and `Esc` cancels
without writing it. In the feedback dialog, `Ctrl+Enter` (or `F5`) submits and
`Esc` returns to the draft. A reviewed file must contain exactly one method
signature; multi-method work must be split into separate runs.

`pipeline.py` runs four durable stages:

1. Formalize the reviewed text as a type-checked Lean/Velvet contract.
2. `VelvetProgrammerAgent`
3. `VelvetInvariantInferrerAgent`
4. `VelvetProofOrchestratorAgent`

Shared prover, reasoning, retrieval, Lean build, token accounting, session
logging, and DBOS recovery services are initialized through `container.py`.

The pipeline is intentionally headless so each invocation can run in a
disposable sandbox:

```bash
uv run lloom-agent pipeline \
  --input-file <reviewed-specification.txt> \
  --output-file <candidate.lean> \
  --provider <openai|google|anthropic> \
  --model <model>
```

To bypass formalization and use an existing Lean/Velvet contract, pass
`--start codegen`. The project defaults to the current directory and a fresh
pipeline run generates and prints its session ID. Use explicit `--project` and
`--session-name` values for orchestrated runs or `--session-name <id> --resume`
to continue prior work. Every formal contract is preserved under the session's
`contracts/` directory, and its SHA-256 is included in the result JSON.

Each pipeline run also atomically publishes
`.lloom/sessions/<session>/<output-stem>_result.json` using result schema
version `1`. Its top-level status progresses from `RUNNING` to `SUCCESS` or
`FAILED`; it records contract and implementation hashes, test/PBT/proof
summaries, per-stage statuses, and structured failure details. Checks skipped
by a partial run remain `null`.

The worker also retains:

- `lean-synth` for direct Lean synthesis and verification.
- `prove-from-file` for filling proof obligations in an existing Lean file.
- `workflows` and `query` for durable-state and analytics inspection.
- `search` for LeanExplore theorem search.

Research datasets, benchmark runners, the former multi-agent specification
stack, external prover services, and non-core command UIs are intentionally
excluded.
