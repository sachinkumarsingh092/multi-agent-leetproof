## LeetProof

This directory contains two subdirectories.

- **leetproof** : This has the code for the tool.
- **llmgen-experiment**: This has the artefact of all the results submitted as part of the paper.

### llmgen-experiment

Inside the directory, the artefacts are split across the following directories.

- **VerinaSpecEquivCheck**  : This has the results of spec equivalence done using Aristotle.
- **SpecPBTResult** : This is from our runs of PBT on specification on CLEVER and Verina benchmarks.
- **verina_feedback.pdf** : This is the report sent for problems found in the Verina benchmarks.
- **clever_feedback.pdf**: This is the report sent for problems found in the CLEVER benchmarks.
- **llmgen/gpt_result** : Contains all the programs generated using GPT 5.2.
- **llmgen/opus_result** : Contains all the programs generated using Opus 4.6.
- **llmgen/problems**: Contains all the problem description and the specification we generated for them.
- **Extensions** : This contains all the Lean programs (extensions) we used for our experiments (example: PBT).

### Running LeetProof

#### Setup
Run the setup script from the repository root:

```bash
bash setup.sh
```

This bootstraps the Python environment in `leetproof/`, builds the Lean project in `llmgen-experiment/`, and downloads the search/model assets used by the tool. No submodule initialization is required.

#### Prerequisites
Before running the tool, make sure the following are available:

- `git`
- `curl`
- Python `3.13+`
- [`uv`](https://github.com/astral-sh/uv) for Python dependency management
- [`elan`](https://github.com/leanprover/elan) for managing the Lean toolchain

The bootstrap script at `setup.sh` installs or configures the expected Lean toolchain (`v4.24.0`), Python dependencies, and the Lean project assets used by LeetProof.

You will also need at least one LLM provider API key before running the pipeline:

```bash
export ANTHROPIC_API_KEY="your-key"
# or
export OPENAI_API_KEY="your-key"
```

#### Commands
From `llmgen-experiment/`, run commands with `./leetproof.sh`:

Keep generated files under `llmgen/`. This directory is already wired into the Lean project; writing specs or outputs outside `llmgen/` can cause import/build failures.

Pipeline usage from a natural-language problem statement:

```bash
bash ./leetproof.sh pipeline \
  --project . \
  --input-file sliding_window_maximum.txt \
  --output-file llmgen/SlidingWindowMaximum.lean \
  --provider <provider> \
  --model <model>
```

Generate only the specification first:

```bash
bash ./leetproof.sh pipeline \
  --project . \
  --end specgen \
  --input-file sliding_window_maximum.txt \
  --output-file llmgen/SlidingWindowMaximumSpec.lean \
  --provider <provider> \
  --model <model>
```

Later, continue from that generated specification:

```bash
bash ./leetproof.sh pipeline \
  --project . \
  --start codegen \
  --input-file llmgen/SlidingWindowMaximumSpec.lean \
  --output-file llmgen/SlidingWindowMaximum.lean \
  --provider <provider> \
  --model <model>
```

Standalone Lean synthesis and verification from an existing specification:

```bash
bash ./leetproof.sh lean-synth \
  --project . \
  --input-file llmgen/SlidingWindowMaximumSpec.lean \
  --output-file llmgen/SlidingWindowMaximumLeanImpl.lean \
  --session-name <session-name> \
  --provider <provider> \
  --model <model>
```

**NOTE**: If you want to add a max-cost on any of these runs, you can append `--max-cost 5` flag to limit at `5$`.

**NOTE**: The max-cost feature requires having the pricing information for the provider+model in `leetproof/config/model_pricing.json`, and it might not have the 
pricing for all models. We currently only have it for a few of them. One can easily add the pricing configuration there to make max-cost work with their model of
choice.
