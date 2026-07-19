#!/bin/sh
set -eu

PROJECT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
ELAN_HOME="$PROJECT_DIR/.tools/elan"
ELAN_ARCHIVE="$PROJECT_DIR/.downloads/elan-aarch64-apple-darwin.tar.gz"
ELAN_UNPACK="$PROJECT_DIR/.downloads/elan-unpack"

mkdir -p "$PROJECT_DIR/.downloads" "$ELAN_UNPACK"

uv sync --project "$PROJECT_DIR" --python 3.12
uv run --project "$PROJECT_DIR" python "$PROJECT_DIR/scripts/fetch_assets.py"
uv run --project "$PROJECT_DIR" python "$PROJECT_DIR/scripts/prepare_data.py"

if [ ! -x "$ELAN_HOME/bin/elan" ]; then
  curl -fL --retry 3 \
    "https://github.com/leanprover/elan/releases/download/v4.2.3/elan-aarch64-apple-darwin.tar.gz" \
    -o "$ELAN_ARCHIVE"
  tar -xzf "$ELAN_ARCHIVE" -C "$ELAN_UNPACK"
  ELAN_HOME="$ELAN_HOME" "$ELAN_UNPACK/elan-init" -y --no-modify-path --default-toolchain none
fi

ELAN_HOME="$ELAN_HOME" "$ELAN_HOME/bin/elan" toolchain install leanprover/lean4:v4.28.0

cd "$PROJECT_DIR/verifier"
ELAN_HOME="$ELAN_HOME" "$ELAN_HOME/bin/lake" update
ELAN_HOME="$ELAN_HOME" "$ELAN_HOME/bin/lake" exe cache get
ELAN_HOME="$ELAN_HOME" "$ELAN_HOME/bin/lake" build

uv run --project "$PROJECT_DIR" python "$PROJECT_DIR/scripts/verify_bootstrap.py"
uv run --project "$PROJECT_DIR" python "$PROJECT_DIR/scripts/smoke_model.py"

