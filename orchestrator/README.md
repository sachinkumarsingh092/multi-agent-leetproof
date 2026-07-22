# LeetProof orchestrator

The orchestrator is external to the LeetProof worker. Step 1 defines the
versioned, human-reviewable job manifest that later sandbox and scheduling
layers will consume.

Each task represents one reviewed, single-method specification:

```json
{
  "$schema": "job.schema.json",
  "schema_version": 1,
  "job_id": "example-job",
  "tasks": [
    {
      "id": "maximum",
      "input_file": "specs/maximum.txt",
      "input_sha256": "<lowercase SHA-256>",
      "output_file": "artifacts/Maximum.lean",
      "depends_on": []
    },
    {
      "id": "summary",
      "input_file": "specs/summary.txt",
      "input_sha256": "<lowercase SHA-256>",
      "output_file": "artifacts/Summary.lean",
      "depends_on": [
        "maximum"
      ]
    }
  ]
}
```

Paths are relative to the manifest directory and cannot escape it. Loading a
manifest verifies every input file and hash, rejects duplicate IDs or outputs,
checks dependencies, rejects cycles, and provides a deterministic topological
execution order. No worker starts until all validation succeeds.

Run the Step 1 tests from the repository root:

```bash
uv run --project leetproof pytest orchestrator/tests -q
```

## Step 2: one-task Docker sandbox

Build the worker image from the repository root:

```bash
docker build \
  --file orchestrator/docker/Dockerfile \
  --tag leetproof-worker:1 \
  .
```

Run a single-task manifest:

```bash
uv run --project leetproof python -m orchestrator /path/to/job.json \
  --provider openai \
  --model <model> \
  --image leetproof-worker:1
```

For a multi-task manifest, select one task with `--task-id <id>`. The matching
provider API key must be present in the host environment; Docker receives its
name without embedding the secret value in the command line.

By default, optional LeanExplore retrieval is disabled inside the sandbox. To
use existing read-only search assets:

```bash
uv run --project leetproof python -m orchestrator /path/to/job.json \
  --provider openai \
  --model <model> \
  --lean-explore-directory ~/.lean_explore \
  --huggingface-cache-directory ~/.cache/huggingface
```

Each run uses a non-root container with dropped capabilities, no-new-privileges,
bounded CPU, memory and process counts, a read-only input specification, and
an ephemeral container filesystem. Only task artifacts and `.lloom` state are
written to `.orchestrator/runs/<job-id>/<task-id>-<attempt>/` beside the
manifest. The container is removed after it exits; failed run data is retained
for diagnosis.

## Multi-method POC

The POC adds one planning call above the existing single-method workers. Start
from a small project request:

```bash
uv run --project leetproof python -m orchestrator.poc plan project.txt \
  --output-directory my-plan \
  --project-id my-plan \
  --provider openai \
  --model <model>
```

This writes `my-plan/plan.json`, a copy of the project request, and one
single-method file under `my-plan/specs/` for every task. Nothing runs yet.
Review and edit all of these files before approval.

Run the approved plan:

```bash
uv run --project leetproof python -m orchestrator.poc run my-plan/plan.json \
  --provider openai \
  --model <model> \
  --image leetproof-worker:1 \
  --max-workers 2
```

The run command freezes task hashes into `job.json`, executes at most two ready
DAG tasks concurrently, and stops releasing dependent tasks after a failure.
Every worker result must report successful tests, PBT, proof generation, and
all four pipeline stages. The gate independently verifies the implementation
and frozen-contract hashes and rejects `sorry` or `admit`.

After all tasks pass, the orchestrator copies the accepted Lean files into a
clean attempt directory, generates one module that imports every result, and
runs `lake env lean` inside the worker image with networking disabled. The
final `integration_result.json` records all accepted hashes.

Integrated copies place each worker's declarations in its own
`Generated.<Module>` namespace so generic names such as `precondition` and
`postcondition` cannot collide. Their proofs are checked again during
integration. The PBT command is not rerun in the namespaced copy because the
result gate already requires PBT success for the immutable source artifact;
both the source and integrated-copy hashes are recorded.

A reviewed three-method example is included, so the scheduler can be tested
without making the planner call:

```bash
uv run --project leetproof python -m orchestrator.poc run \
  orchestrator/examples/tiny-numeric/plan.json \
  --provider openai \
  --model <model> \
  --image leetproof-worker:1
```

POC limit: `depends_on` currently controls scheduling only. Dependency
artifacts are not mounted into downstream workers, so each method
specification must remain self-contained. The final import build catches
module-level composition errors after all workers pass.
