# Multi agent leetProof

Multi agent leetProof turns a natural language project request into separate verified Lean modules and checks that the modules compile together.

## Prerequisites

- Docker
- Python 3.13 or newer
- [uv](https://docs.astral.sh/uv/)
- An OpenAI, Anthropic, or Google API key

## Setup

Run from the repository root:

```bash
uv sync --project leetproof

docker pull sachinkumarsingh092/leetproof-worker:0.1.0
```

To build the worker image locally instead:

```bash
docker build \
  --file orchestrator/docker/Dockerfile \
  --tag leetproof-worker:1 \
  .
```

Set the key for your provider:

```bash
export OPENAI_API_KEY=<key>
```

Use `ANTHROPIC_API_KEY` or `GOOGLE_API_KEY` for the other providers.

## Run

Write the project request in a text file such as `request.txt`.

Generate a reviewable plan:

```bash
uv run --project leetproof python -m orchestrator.poc plan request.txt \
  --output-directory my-project \
  --project-id my-project \
  --provider openai \
  --model <model>
```

Review `my-project/plan.json` and every file under `my-project/specs/`.

Run the approved plan:

```bash
uv run --project leetproof python -m orchestrator.poc run \
  my-project/plan.json \
  --provider openai \
  --model <model> \
  --image sachinkumarsingh092/leetproof-worker:0.1.0 \
  --max-workers 2
```

Worker runs are stored under `my-project/.orchestrator/runs/`. Combined results are stored under `my-project/.orchestrator/integrations/`. A completed run has `"status": "SUCCESS"` in `integration_result.json`.

## Current state

The planner splits a project into single-method tasks. Docker workers generate formal contracts, implementations, tests, property tests, and proofs with the help of the leetproof engine. The result gate checks hashes and rejects incomplete proofs. The integrator places accepted modules in separate namespaces and verifies them together. The current integrator combines verified modules through imports only and doesn't work a glue agent or anything.
