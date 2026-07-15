#!/bin/sh
# Wrapper script for running lloom-agent via uvx from GitHub.
# Usage: ./run-lloom.sh [args...]
#
# Override the branch/ref by setting LLOOM_REF:
#   LLOOM_REF=my-branch ./run-lloom.sh bench problems.json --project .

LLOOM_REF="${LLOOM_REF:-main}"
LLOOM_REPO="${LLOOM_REPO:-git+https://github.com/verse-lab/lloom}"

exec uvx --from "${LLOOM_REPO}@${LLOOM_REF}" lloom-agent "$@"
