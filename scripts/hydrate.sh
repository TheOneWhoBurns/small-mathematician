#!/bin/sh
set -eu

PROJECT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
uv sync --project "$PROJECT_DIR" --python 3.12
exec uv run --project "$PROJECT_DIR" python "$PROJECT_DIR/scripts/hydrate.py" "$@"
