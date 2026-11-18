.PHONY: help lint lint-check typecheck test check-pinning verify format

help:
	@echo "cloud - Makefile commands"
	@echo "──────────────────────────────────────────────────────"
	@echo "  make lint          - Fix linting issues with ruff"
	@echo "  make lint-check    - Check linting without fixing"
	@echo "  make typecheck     - Run ty type checker"
	@echo "  make test          - Run the test suite"
	@echo "  make check-pinning - Check make_pinned_ssl_context against the canonical snippet"
	@echo "  make verify        - Run all checks (lint + typecheck + test)"
	@echo "  make format        - Format with ruff"

lint:
	uv run ruff check --fix; uv run ruff format

lint-check:
	uv run ruff check --no-fix && uv run ruff format --check

typecheck:
	uv run ty check

test:
	uv run python test.py

check-pinning:
	python3 scripts/check_pinning.py

verify: lint-check typecheck test

format:
	uv run ruff format
