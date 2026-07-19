#!/usr/bin/env python3
"""Prepare matched statement/blueprint inputs for a downstream proof writer."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--view", type=Path, required=True)
    parser.add_argument("--baseline-blueprints", type=Path, required=True)
    parser.add_argument("--trained-blueprints", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()

    baseline_rows = read_jsonl(args.baseline_blueprints)
    trained_rows = read_jsonl(args.trained_blueprints)
    baseline = {row["id"]: row["response"] for row in baseline_rows}
    trained = {row["id"]: row["response"] for row in trained_rows}
    if set(baseline) != set(trained):
        raise ValueError("blueprint prediction IDs differ")

    references = {
        row["metadata"]["id"]: row
        for row in read_jsonl(args.view / "valid.jsonl")
    }
    ids = [row["id"] for row in baseline_rows]
    common = [
        {
            "id": example_id,
            "family_id": references[example_id]["metadata"]["family_id"],
            "problem": references[example_id]["prompt"],
        }
        for example_id in ids
    ]
    write_jsonl(args.output_dir / "statement-only.jsonl", common)
    write_jsonl(
        args.output_dir / "baseline-blueprint.jsonl",
        [row | {"blueprint": baseline[row["id"]]} for row in common],
    )
    write_jsonl(
        args.output_dir / "trained-blueprint.jsonl",
        [row | {"blueprint": trained[row["id"]]} for row in common],
    )
    manifest = {
        "schema_version": 1,
        "rows": len(ids),
        "view": str(args.view),
        "valid_sha256": sha256(args.view / "valid.jsonl"),
        "baseline_blueprints": str(args.baseline_blueprints),
        "baseline_blueprints_sha256": sha256(args.baseline_blueprints),
        "trained_blueprints": str(args.trained_blueprints),
        "trained_blueprints_sha256": sha256(args.trained_blueprints),
        "reference_proofs_exposed_to_formalizer": False,
    }
    (args.output_dir / "manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
