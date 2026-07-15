#!/bin/bash
set -euo pipefail

# =============================================================================
# LeetProof setup script
# Idempotent and intended to run from the repository root.
#
# This handles:
#   1. System deps + uv + Python deps for leetproof/
#   2. elan + Lean toolchain
#   3. Lean project build for llmgen-experiment/
#   4. Search data + embedding models (via leetproof/cli.py setup)
# =============================================================================

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TOOL_DIR="${ROOT_DIR}/leetproof"
LEAN_PROJECT_DIR="${ROOT_DIR}/llmgen-experiment"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

step() { echo -e "\n${BLUE}==> $1${NC}"; }
ok()   { echo -e "${GREEN}    OK: $1${NC}"; }
warn() { echo -e "${YELLOW}    WARN: $1${NC}"; }
err()  { echo -e "${RED}    ERROR: $1${NC}"; }

# =============================================================================
# 0. Check repository layout
# =============================================================================
step "Checking repository layout"

if [ ! -f "${TOOL_DIR}/pyproject.toml" ]; then
    err "Expected Python project at ${TOOL_DIR}"
    exit 1
fi

if [ ! -f "${LEAN_PROJECT_DIR}/lakefile.toml" ] && [ ! -f "${LEAN_PROJECT_DIR}/lakefile.lean" ]; then
    err "Expected Lean project at ${LEAN_PROJECT_DIR}"
    err "This repository should already contain llmgen-experiment/; no submodule init is performed."
    exit 1
fi

if [ ! -f "${LEAN_PROJECT_DIR}/lean-toolchain" ]; then
    err "Missing ${LEAN_PROJECT_DIR}/lean-toolchain"
    exit 1
fi

LEAN_TOOLCHAIN="$(tr -d '\n' < "${LEAN_PROJECT_DIR}/lean-toolchain")"
LEAN_VERSION="${LEAN_TOOLCHAIN##*:}"

ok "Found leetproof/ and llmgen-experiment/"
ok "Lean toolchain: ${LEAN_TOOLCHAIN}"

# =============================================================================
# 1. Check system dependencies
# =============================================================================
step "Checking system dependencies"

for cmd in git curl; do
    if command -v "$cmd" >/dev/null 2>&1; then
        ok "$cmd found"
    else
        err "$cmd not found. Please install it first."
        exit 1
    fi
done

# =============================================================================
# 2. Install uv
# =============================================================================
step "Checking uv"

if command -v uv >/dev/null 2>&1; then
    ok "uv found ($(uv --version))"
else
    echo "    Installing uv..."
    curl -LsSf https://astral.sh/uv/install.sh | sh
    export PATH="$HOME/.local/bin:$PATH"
    ok "uv installed ($(uv --version))"
fi

# =============================================================================
# 3. Install Python dependencies
# =============================================================================
step "Installing Python dependencies"

if [ -d "${TOOL_DIR}/.venv" ] && (cd "${TOOL_DIR}" && uv run python -c "import langchain" >/dev/null 2>&1); then
    ok "Python dependencies already installed"
else
    echo "    Running uv sync in leetproof/..."
    (cd "${TOOL_DIR}" && uv sync)
    ok "Python dependencies installed"
fi

# =============================================================================
# 4. Install elan + Lean toolchain
# =============================================================================
step "Checking elan and Lean"

if command -v elan >/dev/null 2>&1; then
    ok "elan found ($(elan --version 2>/dev/null | head -1))"
else
    echo "    Installing elan (Lean version manager)..."
    curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain "${LEAN_TOOLCHAIN}"
    export PATH="$HOME/.elan/bin:$PATH"
    ok "elan installed"
fi

# Ensure elan-installed shims are reachable even if the current shell did not
# source elan's env setup yet.
if [ -d "$HOME/.elan/bin" ] && [[ ":$PATH:" != *":$HOME/.elan/bin:"* ]]; then
    export PATH="$HOME/.elan/bin:$PATH"
fi

if elan toolchain list | grep -Fq "${LEAN_TOOLCHAIN}"; then
    ok "Lean ${LEAN_VERSION} toolchain already installed"
else
    echo "    Installing Lean ${LEAN_TOOLCHAIN}..."
    elan toolchain install "${LEAN_TOOLCHAIN}"
    ok "Lean ${LEAN_VERSION} installed"
fi

if command -v lean >/dev/null 2>&1; then
    ok "lean found ($(cd "${LEAN_PROJECT_DIR}" && lean --version 2>/dev/null | head -1 || true))"
else
    warn "lean is not currently on PATH; try opening a new shell after elan install"
fi

if command -v lake >/dev/null 2>&1; then
    ok "lake found"
else
    warn "lake is not currently on PATH; builds may fail until elan's bin dir is on PATH"
fi

# =============================================================================
# 5. Build Lean project
# =============================================================================
step "Building Lean project (llmgen-experiment/)"

if [ -d "${LEAN_PROJECT_DIR}/.lake/build" ] && [ -d "${LEAN_PROJECT_DIR}/.lake/packages" ]; then
    ok "Lean project already built"
else
    echo "    Fetching Mathlib cache (avoids compiling from source)..."
    (cd "${LEAN_PROJECT_DIR}" && lake exe cache get)
    echo "    Building Lean project (may take 15-30 minutes on first run)..."
    (cd "${LEAN_PROJECT_DIR}" && lake build)
    ok "Lean project built"
fi

# =============================================================================
# 6. Setup search data + embedding models
# =============================================================================
step "Setting up search tools and models"

echo "    This downloads Loogle (~100MB), LeanExplore (~8GB), and BGE model (~400MB)"
(cd "${TOOL_DIR}" && uv run python cli.py setup)

# =============================================================================
# Done
# =============================================================================
echo ""
echo -e "${GREEN}========================================${NC}"
echo -e "${GREEN}  Setup complete!${NC}"
echo -e "${GREEN}========================================${NC}"
