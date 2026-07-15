#!/usr/bin/env python3
"""Entry point for running LeanSynthAndVerifyAgent standalone.

This script imports the agent module properly (avoiding __main__ issues with DBOS)
and then calls its main() function.

Usage:
    uv run lean_synth_and_verify.py --provider openai --model gpt-4 --input-file spec.lean
"""

# Import the module under its canonical name (not as __main__)
from agents.lean_synth_and_verify import main

if __name__ == "__main__":
    main()
