.PHONY: build clean clean-all clean-venv clean-search install dev typecheck help setup

# Default target
help:
	@echo "Available targets:"
	@echo "  setup             - Full setup from fresh clone (does everything)"
	@echo "  install           - Install dependencies with uv"
	@echo "  build             - Build standalone binary with PyInstaller"
	@echo "  dev               - Install dev dependencies"
	@echo "  typecheck         - Run type checking"
	@echo "  clean             - Remove build artifacts and pycache"
	@echo "  clean-venv        - Remove virtual environment"
	@echo "  clean-search      - Remove LeanExplore data"
	@echo "  clean-all         - Remove everything (venv, build, search data)"

# Full setup from fresh clone
setup:
	bash ../setup.sh

# Install dependencies
install:
	uv sync

# Install dev dependencies (including PyInstaller)
dev:
	uv sync --extra dev

typecheck:
	@echo "Running type checking with ty..."
	uvx ty check --exclude 'llmgen-experiments/CaseStudies/'

# Build standalone binary
build:
	uv run pyinstaller lloom-agent.spec

# Clean build artifacts
clean:
	rm -rf build dist __pycache__
	rm -rf *.egg-info
	find . -type d -name "__pycache__" -exec rm -rf {} + 2>/dev/null || true
	find . -type f -name "*.pyc" -delete 2>/dev/null || true

# Clean virtual environment
clean-venv:
	rm -rf .venv

# Clean search tool data (LeanExplore)
clean-search:
	@echo "Removing LeanExplore data..."
	rm -rf ~/.lean_explore
	@echo "Search data cleaned!"

# Clean everything
clean-all: clean clean-venv clean-search
	@echo "All cleaned!"
