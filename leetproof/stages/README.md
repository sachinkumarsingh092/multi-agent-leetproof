# LLoom Pipeline Stages

This directory contains the modular stages of the LLoom pipeline. Each stage is self-contained and exports a `create_*_workflow()` function that returns a compiled LangGraph StateGraph.

## Important: Execution Context

⚠️ **The pipeline must be executed from the Lean project root directory (`llmgen-experiments`)**, not from the `lloom-agent` directory. This is required because:
- `lake build` commands need access to `lakefile.toml`
- Lean file paths are resolved relative to the Lean project root
- The Lean toolchain and dependencies are configured at the project level

## Pipeline Architecture

The complete pipeline consists of 5 sequential stages:

```
1. Specification Generation
   ↓
2. Specification Validation
   ↓
3. Code Generation
   ↓
4. Invariant Generation
   ↓
5. Verification
```

## Stage Details

### 1. Specification Generation (`spec_generate.py`)

**Purpose**: Generate a formal Lean specification from a natural language problem description.

**Input**:
- `SpecAgentState` with `problem_description`, `problem_id`, `output_file`

**Process**:
1. Generate specification (SpecGenAgent)
2. Typecheck specification
3. Coach review (SpecCoachAgent)
4. Optional conciseness fix
5. Retry if rejected by coach

**Output**:
- Typechecked Lean specification file
- Coach verdict and feedback

**Key Nodes**:
- `generate_spec` - SpecGenAgent generates initial specification
- `typecheck_spec` - Runs Lean typechecker
- `coach_spec` - SpecCoachAgent reviews and scores
- `apply_conciseness_fix` - Optional refinement based on coach feedback

---

### 2. Specification Validation (`spec_validate.py`)

**Purpose**: Validate the specification by proving concrete examples.

**Input**:
- `SpecAgentState` with generated specification

**Process**:
1. Generate example verification file using `example_verify.py` script
2. Prove examples with ExampleProverAgent
3. If proofs fail after 10 attempts, seek ProofGuideAgent assistance
4. Retry with guidance

**Output**:
- Example verification file with proofs
- Proof typecheck status

**Key Nodes**:
- `generate_example_verify` - Creates verification file with test cases
- `prove_examples` - ExampleProverAgent completes proofs (subworkflow)
- `guide_proofs` - ProofGuideAgent provides guidance when stuck

---

### 3. Code Generation (`code_generate.py`)

**Purpose**: Generate Velvet code from the formal specification.

**Input**:
- `VelvetAgentState` with `specification`, `output_file`

**Process**:
1. Generate Velvet program (VelvetProgrammerAgent)
2. Judge review (VelvetJudgeAgent)
3. Retry if rejected

**Output**:
- Velvet program file
- Judge verdict

**Key Nodes**:
- `generate_velvet_program` - VelvetProgrammerAgent writes code
- `judge_velvet_program` - VelvetJudgeAgent reviews quality

---

### 4. Invariant Generation (`invariant_generate.py`)

**Purpose**: Improve and refine loop invariants in the Velvet program.

**Input**:
- `VelvetAgentState` with generated Velvet program

**Process**:
1. Improve invariants (VelvetInvariantInferrer)
2. Prepare judge context with programmer's stable version
3. Judge review (VelvetJudgeAgent)
4. If rejected, revert to stable version and retry

**Output**:
- Velvet program with improved invariants
- Judge verdict

**Key Nodes**:
- `improve_invariants` - VelvetInvariantInferrer refines loop invariants
- `prepare_judge_context_inferrer` - Injects programmer's version for comparison
- `judge_invariants` - VelvetJudgeAgent reviews invariant quality
- `revert_stable_on_inferrer_fail` - Restores last good version on failure

---

### 5. Verification (`verification.py`)

**Purpose**: Generate and assemble formal proofs for the Velvet program.

**Input**:
- `VelvetAgentState` with program and invariants

**Process**:
1. Proof reasoning - analyze and decompose proof goals (VelvetProofReasoningAgent)
2. Proof conversion - convert reasoning to Lean code (VelvetProofConverterAgent)
3. Proof assembly - assemble final proof (VelvetProofAssemblerAgent)
4. Final verification - run Lean typechecker

**Output**:
- Complete verified Velvet program with proofs
- Final verification status

**Key Nodes**:
- `proof_reasoning` - VelvetProofReasoningAgent decomposes proof
- `proof_conversion` - VelvetProofConverterAgent converts to Lean
- `assemble_final_proof` - VelvetProofAssemblerAgent assembles
- `final_verification` - Final typecheck

---

## Usage

### Running Individual Stages

Each stage can be run independently for testing:

```python
from stages.spec_generate import create_spec_generate_workflow
from agents.spec_state import SpecAgentState

# Create workflow
workflow = create_spec_generate_workflow()

# Create initial state
state = SpecAgentState(
    problem_description="Write a function that...",
    problem_id="test_01",
    output_file="output/spec.lean",
    # ... other fields
)

# Run the stage
result = await workflow.ainvoke(state)
```

### Running Complete Pipeline

Use `pipeline.py` to run all stages or partial stages:

```bash
# Run complete pipeline from problem description (--start defaults to specgen)
uv run pipeline.py \
  --input-file examples/problem_prime_check.txt \
  --output-file output/prime.lean

# Run from specification validation onwards
uv run pipeline.py \
  --start specvalid \
  --input-file output/prime_spec.lean \
  --output-file output/prime_impl.lean

# Run only code generation
uv run pipeline.py \
  --start codegen \
  --end codegen \
  --input-file output/prime_spec.lean \
  --output-file output/prime_code.lean

# Run invariant generation and verification
uv run pipeline.py \
  --start invgen \
  --input-file output/prime_code.lean \
  --output-file output/prime_verified.lean
```

### Visualizing Stage Graphs

```bash
# Print all stages (default)
uv run pipeline.py --print-graph

# Print specific stages
uv run pipeline.py --start codegen --end invgen --print-graph
```

This will print ASCII visualizations of the specified stage workflow(s).

## State Transitions

The pipeline handles two main state types:

1. **SpecAgentState** (Stages 1-2)
   - Used for specification generation and validation
   - Contains: problem description, spec content, coach feedback, etc.

2. **VelvetAgentState** (Stages 3-5)
   - Used for code generation, invariants, and verification
   - Contains: specification, program code, proof analysis, etc.

The transition happens in `pipeline.py` at the `transition_spec_to_code` node, which:
- Reads the generated specification file
- Creates a new VelvetAgentState with the specification
- Determines the implementation output file path
- Sets up write restrictions for the implementation phase

## Benefits of Modular Design

1. **Self-contained**: Each stage is independent and can be tested/modified separately
2. **Reusable**: Stages can be composed in different pipelines
3. **Maintainable**: Clear separation of concerns, easier to debug
4. **Testable**: Each stage can be unit tested independently
5. **No circular dependencies**: pipeline.py doesn't depend on main.py or spec_main.py

## Development Guidelines

When modifying stages:

1. Keep stages self-contained - all logic should be in the stage file
2. Export only the `create_*_workflow()` function
3. Use clear logging at stage boundaries
4. Handle state transitions carefully
5. Add retry logic where appropriate
6. Document state input/output requirements
