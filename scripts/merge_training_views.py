#!/usr/bin/env python3
"""Merge immutable JSONL training views with duplicate-ID rejection."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--train", type=Path, nargs="+", required=True)
    parser.add_argument("--valid", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    train_rows = [row for path in args.train for row in read(path)]
    valid_rows = read(args.valid)
    train_ids = [row.get("metadata", {}).get("id") for row in train_rows]
    valid_ids = [row.get("metadata", {}).get("id") for row in valid_rows]
    if any(not isinstance(example_id, str) for example_id in train_ids + valid_ids):
        raise ValueError("every row must have metadata.id")
    if len(train_ids) != len(set(train_ids)):
        raise ValueError("duplicate training IDs")
    if set(train_ids) & set(valid_ids):
        raise ValueError("train/valid ID overlap")

    args.output.mkdir(parents=True, exist_ok=True)
    for split, rows in (("train", train_rows), ("valid", valid_rows)):
        output = args.output / f"{split}.jsonl"
        with output.open("w", encoding="utf-8") as handle:
            for row in rows:
                handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
    manifest = {
        "schema_version": 1,
        "train_sources": [{"path": str(path), "sha256": sha256(path)} for path in args.train],
        "valid_source": {"path": str(args.valid), "sha256": sha256(args.valid)},
        "counts": {"train": len(train_rows), "valid": len(valid_rows)},
        "duplicate_ids": 0,
        "train_valid_overlap": 0,
    }
    (args.output / "manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
