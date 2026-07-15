# Evaluation Benchmarks

Two benchmark datasets are available for evaluation:

1. **VERINA** - 189 problems with Lean specifications (108 basic + 81 advanced)
2. **MBPP-San-Velvet-228** - 228 general programming problems with Velvet specifications

---

## VERINA Benchmark

### Basic Usage

```bash
uv run python evals/verina.py basic 1
uv run python evals/verina.py advanced 25 -c description signature
uv run python evals/verina.py basic 1 -c description -f text
```

### Command Format

```bash
uv run python evals/verina.py <difficulty> <number> [OPTIONS]
```

**Arguments:**
- `difficulty`: `basic` (problems 1-108) or `advanced` (problems 1-81)
- `number`: Problem number

**Options:**
- `-c, --components`: Extract specific fields (omit for all)
- `-f, --format`: `json` (default) or `text`

### Available Components

`problem_id`, `description`, `signature`, `precond_desc`, `postcond_desc`, `precond`, `postcond`, `code`, `proof`, `precond_aux`, `postcond_aux`, `code_aux`, `proof_aux`, `task_imports`, `solution_imports`, `python_reference`, `tests`, `reject_inputs`, `metadata`

### Examples

Get a problem with selected fields:
```bash
$ uv run python evals/verina.py basic 1 -c problem_id code signature
{
  "problem_id": "verina_basic_1",
  "code": "a * b < 0",
  "signature": {
    "name": "hasOppositeSign",
    "parameters": [
      {"param_name": "a", "param_type": "Int"},
      {"param_name": "b", "param_type": "Int"}
    ],
    "return_type": "Bool"
  }
}
```

Get description and precondition:
```bash
$ uv run python evals/verina.py basic 1 -c description precond_desc
{
  "description": "This task requires writing a Lean 4 method that determines whether two given integers have opposite signs...",
  "precond_desc": "- There are no preconditions, the method will always work."
}
```

Get test cases:
```bash
$ uv run python evals/verina.py basic 1 -c tests
{
  "tests": [
    {"input": [1, -1], "output": true},
    {"input": [2, 3], "output": false},
    {"input": [-5, 4], "output": true}
  ]
}
```

Get in text format:
```bash
$ uv run python evals/verina.py basic 1 -c description -f text
=== DESCRIPTION ===
This task requires writing a Lean 4 method that determines whether two given integers have opposite signs...
```

---

## MBPP-San-Velvet-228 Benchmark

### Basic Usage

```bash
uv run python evals/mbpp.py 1
uv run python evals/mbpp.py 25 -c task_description method_signature
uv run python evals/mbpp.py 1 -c test_cases -f text
```

### Command Format

```bash
uv run python evals/mbpp.py <number> [OPTIONS]
```

**Arguments:**
- `number`: Problem position (1-228, sorted by task ID for consistency)

**Options:**
- `-c, --components`: Extract specific fields (omit for all)
- `-f, --format`: `json` (default) or `text`

### Available Components

`task_id`, `task_description`, `method_signature`, `test_cases`

### Examples

Get a problem with selected fields:
```bash
$ python3 evals/mbpp.py 1 -c task_id task_description method_signature
{
  "task_id": "2",
  "task_description": "Write a method in Velvet to find the shared elements from the given two array.",
  "method_signature": "method similarElements (arr1:array<int>, arr2:array<int>) returns (res: array<int>)"
}
```

Get test cases:
```bash
$ python3 evals/mbpp.py 1 -c test_cases
{
  "test_cases": {
    "test_1": "var a1:= new int[] [3, 4, 5, 6];\nvar a2:= new int[] [5, 7, 4, 10];\nvar e1:= new int[] [4, 5];\nvar res1:=similarElements(a1,a2);\nassert arrayEquals(res1,e1);",
    "test_2": "var a3:= new int[] [1, 2, 3, 4];\nvar a4:= new int[] [5, 4, 3, 7];\nvar e2:= new int[] [3, 4];\nvar res2:=similarElements(a3,a4);\nassert arrayEquals(res2,e2);",
    "test_3": "var a5:= new int[] [11, 12, 14, 13];\nvar a6:= new int[] [17, 15, 14, 13];\nvar e3:= new int[] [13, 14];\nvar res3:=similarElements(a5,a6);\nassert arrayEquals(res3,e3);"
  }
}
```

Get in text format:
```bash
$ python3 evals/mbpp.py 1 -c task_description -f text
=== TASK_DESCRIPTION ===
Write a method in Velvet to find the shared elements from the given two array.
```

---

## Integration

### Python

```python
import subprocess
import json

# Get a VERINA problem
result = subprocess.run([
    "python3", "evals/verina.py", "basic", "1", "-c", "code", "tests"
], capture_output=True, text=True)
problem = json.loads(result.stdout)
print(f"Code: {problem['code']}")

# Get an MBPP problem
result = subprocess.run([
    "python3", "evals/mbpp.py", "1", "-c", "task_description"
], capture_output=True, text=True)
problem = json.loads(result.stdout)
print(f"Task: {problem['task_description']}")
```

### Iterate Over Problems

```python
# VERINA: iterate basic problems (1-108)
for i in range(1, 11):
    result = subprocess.run([
        "python3", "evals/verina.py", "basic", str(i), "-c", "problem_id"
    ], capture_output=True, text=True)
    problem = json.loads(result.stdout)
    print(problem['problem_id'])

# MBPP: iterate problems (1-228)
for i in range(1, 11):
    result = subprocess.run([
        "python3", "evals/mbpp.py", str(i), "-c", "task_id"
    ], capture_output=True, text=True)
    problem = json.loads(result.stdout)
    print(problem['task_id'])
```

### Shell / jq

```bash
# Get all VERINA basic problems
for i in {1..10}; do
  python3 evals/verina.py basic $i -c problem_id
done

# Get all MBPP problems
for i in {1..10}; do
  python3 evals/mbpp.py $i -c task_id
done

# Pipe to jq for filtering
python3 evals/verina.py basic 1 | jq '.code'
python3 evals/mbpp.py 1 | jq '.test_cases.test_1'
```

---

## Notes

- **VERINA** auto-clones the benchmark repository on first use (~1.5s). Subsequent runs use the local copy (~50ms).
- **MBPP** problems are indexed by position (1-228) for consistent iteration, though original task IDs are preserved.
- Both return JSON by default. Use `-f text` for human-readable output.
- All "Dafny" references in MBPP have been replaced with "Velvet".
