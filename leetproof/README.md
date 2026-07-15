# LeetProof

LLM-powered verification agent for generating and verifying formal programs in **Velvet**, a hybrid verification language combining SMT solving with Lean proofs.

## Overview

LLoom Agent transforms natural language problem descriptions into fully verified formal programs through a 5-stage pipeline:

1. **specgen** - Generate formal Lean specification from problem description
2. **specvalid** - Validate specification with concrete examples
3. **codegen** - Generate Velvet code implementation
4. **invgen** - Infer loop invariants
5. **verify** - Generate proofs and verify correctness

## Prerequisites

- Python 3.13+
- [uv](https://github.com/astral-sh/uv) - Python package manager
- [elan](https://github.com/leanprover/elan) - Lean version manager

## Setup

From the repository root, run the repository-level setup script:

```bash
bash setup.sh
```

This installs Python dependencies for `leetproof/`, builds the Lean project in `llmgen-experiment/`, and downloads the search/model assets.

## Configuration

Set your LLM provider API key:

```bash
# Pick one (or more) based on your provider
export ANTHROPIC_API_KEY="your-key"
export OPENAI_API_KEY="your-key"
```
