#!/usr/bin/env python3
"""Entry point for running DafnySynthAgent standalone.

This script imports the agent module properly (avoiding __main__ issues with DBOS)
and then calls its main() function.

Usage:
    uv run dafny_synth.py --provider openai --model gpt-4 --input-file spec.lean
"""

# Import the module under its canonical name (not as __main__)
from agents.dafny_synth import main

if __name__ == "__main__":
    main()
