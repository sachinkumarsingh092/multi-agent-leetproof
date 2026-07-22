# Multi agent progress

LeetProof can now turn a natural language project request into a set of
independently verified Lean modules. The system plans the work, gives the user
a review step, runs isolated docker workers, checks their results, and verifies that
the final modules compile together.

## Architecture

```mermaid
flowchart LR
    A[Project request] --> B[Planner]
    B --> C[Human review]
    C --> D[Plan and method specs]
    D --> E[Task scheduler]
    E --> F[Docker workers]
    F --> G[Result gate]
    G --> H[Module integration]
    H --> I[Verified Lean project]
```



The planner reads a short project description and divides it into
single-method tasks. It writes a `plan.json` file and one natural language
specification for each method. Nothing runs until the user reviews these
files.

The plan also records task dependencies. The scheduler uses them to decide
which tasks can run at the same time and which tasks must wait.

## Worker pipeline

Each task runs inside its own Docker container. The worker receives one method
specification and writes to a separate run directory.

```mermaid
flowchart LR
    A[Method specification] --> B[Formal contract]
    B --> C[Implementation]
    C --> D[Loop invariants]
    D --> E[Tests and property tests]
    E --> F[Formal proof]
    F --> G[Result JSON]
```



The formal contract is saved separately and hashed before implementation.
This prevents a later stage from weakening the contract to make the proof
easier.

The worker generates an implementation, concrete tests, property tests, loop
invariants, and a formal proof. Its result file records the contract hash,
implementation hash, test status, proof status, and the outcome of every
pipeline stage.

## Result validation

The result gate accepts a worker only when its tests, property tests, and proof
pass. It checks the recorded hashes against the actual files and rejects Lean
code containing `sorry` or `admit`.

If a task fails, its run directory is kept for inspection. Tasks that depend
on it are not started.

## Integration

Accepted modules are copied into a clean integration directory. Each module
is placed in a namespace such as `Generated.FilterAliveNodes`. This prevents
common names such as `precondition` and `postcondition` from colliding.

```mermaid
flowchart TD
    A[Verified module A] --> D[Namespaced integration]
    B[Verified module B] --> D
    C[Verified module C] --> D
    D --> E[All.lean]
    E --> F[Offline Lean check]
    F --> G[integration_result.json]
```



The integrator recompiles the modules and their proofs with networking
disabled. The source hashes and integrated module hashes are written to
`integration_result.json`.

Property tests are not repeated in the namespaced copy. They have already
passed against the immutable worker artifact. Formal proofs and combined
imports are checked again during integration.

## Current result

The leader election example produced six verified methods for filtering alive
nodes, choosing the highest node ID, counting votes, checking a majority,
finding the next node in a ring, and accepting a newer term.

All six worker results passed their tests, property tests, and proofs. Their
namespaced modules also passed the final combined Lean check.

## Next step

The current `All.lean` file proves that the generated modules can coexist, but
it only imports them. It does not yet connect them into one application.

The next step is a verified glue module. It will call the generated methods in
the correct order, prove that their contracts fit together, and expose a small
public API for the complete program.