#!/usr/bin/env python3
"""Verify pinned files and enforce the natural-language/formal boundary."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LOCK = json.loads((ROOT / "assets" / "sources.lock.json").read_text())
RAW = ROOT / "assets" / "data" / "raw"
PROCESSED = ROOT / "assets" / "data" / "processed"
MODEL = ROOT / "assets" / "models" / "qwen3-0.6b-base"


def digest(path: Path, algorithm: str) -> str:
    hasher = hashlib.new(algorithm)
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(8 * 1024 * 1024), b""):
            hasher.update(chunk)
    return hasher.hexdigest()


def locations() -> dict[str, Path]:
    return {
        "qwen3_0_6b_base": MODEL,
        "naturalproofs_2": RAW / "naturalproofs",
        "fineproofs_sft": RAW / "fineproofs",
        "proofbench": RAW / "proofbench",
        "ma_proofbench": RAW / "ma-proofbench",
    }


def verify_sources() -> int:
    checked = 0
    for source_name, root in locations().items():
        source = LOCK["sources"][source_name]
        for spec in source["files"]:
            path = root / spec["path"]
            if not path.exists():
                raise FileNotFoundError(path)
            if path.stat().st_size != spec["size"]:
                raise ValueError(f"size mismatch: {path}")
            for algorithm in ("sha256", "md5"):
                if spec.get(algorithm) and digest(path, algorithm) != spec[algorithm]:
                    raise ValueError(f"{algorithm} mismatch: {path}")
            checked += 1
    return checked


def verify_boundary() -> int:
    forbidden = re.compile(r"(?m)^\s*(import\s+Mathlib|theorem\s+\w+.*:=\s+by|set_option\s+maxHeartbeats)")
    forbidden_keys = {"formal_statement", "lean_code", "proof_state", "tactic_trace"}
    checked = 0
    for folder in (PROCESSED / "candidates", PROCESSED / "knowledge", PROCESSED / "eval", PROCESSED / "audited"):
        for path in folder.rglob("*.jsonl"):
            with path.open(encoding="utf-8") as handle:
                for line_number, line in enumerate(handle, start=1):
                    if forbidden.search(line):
                        raise ValueError(f"Lean syntax leaked into small-model view: {path}:{line_number}")
                    row = json.loads(line)
                    if forbidden_keys.intersection(row):
                        raise ValueError(f"formal field leaked into small-model view: {path}:{line_number}")
            checked += 1
    return checked


def main() -> None:
    source_count = verify_sources()
    view_count = verify_boundary()
    model_config = json.loads((MODEL / "config.json").read_text())
    if model_config.get("model_type") != "qwen3":
        raise ValueError("unexpected model type")
    print(f"verified pinned files: {source_count}")
    print(f"verified natural-language views: {view_count}")
    print("architecture boundary: PASS")


if __name__ == "__main__":
    main()
