.PHONY: help lint lint-check typecheck check format

help:
	@echo "cloud - Makefile commands"
	@echo "──────────────────────────────────────────────────────"
	@echo "  make lint        - Fix linting issues with ruff"
	@echo "  make lint-check  - Check linting without fixing"
	@echo "  make typecheck   - Run ty type checker"
	@echo "  make check       - Run all checks (lint + typecheck)"
	@echo "  make format      - Format with ruff"

lint:
	uv run ruff check --fix; uv run ruff format

lint-check:
	uv run ruff check --no-fix && uv run ruff format --check

typecheck:
	uv run ty check

check: lint-check typecheck

format:
	uv run ruff format
