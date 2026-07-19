#!/usr/bin/env python3
"""Build a deterministic 1:1 method-routing and numerical-reasoning mix."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import defaultdict
from pathlib import Path


NUMERIC_FAMILIES = (
    "integer_expression",
    "gcd_bezout",
    "modular_inverse",
    "quadratic_integer_roots",
    "linear_system",
)
SEPARATOR = "\nSolution:\n"


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def stable_key(salt: str, value: str) -> str:
    return hashlib.sha256(f"{salt}|{value}".encode()).hexdigest()


def convert_numeric(row: dict) -> dict:
    text = row["text"]
    if text.count(SEPARATOR) != 1:
        raise ValueError("numeric trace must contain exactly one Solution separator")
    before, after = text.split(SEPARATOR)
    source_id = row["metadata"]["synthetic_id"]
    return {
        "prompt": before.rstrip() + SEPARATOR,
        "completion": after.strip(),
        "metadata": {
            **row["metadata"],
            "id": f"numeric-rehearsal-{source_id}",
            "rehearsal_task": "numerical_reasoning",
        },
    }


def sample_numeric(path: Path, per_family: int, split: str) -> list[dict]:
    grouped: dict[str, list[dict]] = defaultdict(list)
    for row in read_jsonl(path):
        grouped[row["metadata"]["family"]].append(row)
    selected: list[dict] = []
    for family in NUMERIC_FAMILIES:
        ranked = sorted(
            grouped[family],
            key=lambda row: stable_key(f"method-numeric-v1|{split}|{family}", row["metadata"]["synthetic_id"]),
        )
        if len(ranked) < per_family:
            raise ValueError(f"need {per_family} {family} rows in {path}, found {len(ranked)}")
        selected.extend(convert_numeric(row) for row in ranked[:per_family])
    return selected


def mark_method(row: dict) -> dict:
    return {
        **row,
        "metadata": {**row["metadata"], "rehearsal_task": "method_routing"},
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--method-view", type=Path, required=True)
    parser.add_argument("--numeric-view", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--numeric-train-per-family", type=int, default=92)
    parser.add_argument("--numeric-valid-per-family", type=int, default=10)
    args = parser.parse_args()

    method_train_path = args.method_view / "train.jsonl"
    method_valid_path = args.method_view / "valid.jsonl"
    numeric_train_path = args.numeric_view / "train.jsonl"
    numeric_valid_path = args.numeric_view / "valid.jsonl"
    method_train = [mark_method(row) for row in read_jsonl(method_train_path)]
    method_valid = [mark_method(row) for row in read_jsonl(method_valid_path)]
    numeric_train = sample_numeric(numeric_train_path, args.numeric_train_per_family, "train")
    numeric_valid = sample_numeric(numeric_valid_path, args.numeric_valid_per_family, "valid")

    splits = {
        "train": method_train + numeric_train,
        "valid": method_valid + numeric_valid,
    }
    for split, rows in splits.items():
        ids = [row["metadata"]["id"] for row in rows]
        if len(ids) != len(set(ids)):
            raise ValueError(f"duplicate IDs in {split}")
        rows.sort(key=lambda row: stable_key(f"method-numeric-v1|order|{split}", row["metadata"]["id"]))

    train_ids = {row["metadata"]["id"] for row in splits["train"]}
    valid_ids = {row["metadata"]["id"] for row in splits["valid"]}
    if train_ids & valid_ids:
        raise ValueError("train/valid overlap")

    args.output.mkdir(parents=True, exist_ok=True)
    output_hashes = {}
    for split, rows in splits.items():
        output = args.output / f"{split}.jsonl"
        with output.open("w", encoding="utf-8") as handle:
            for row in rows:
                handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
        output_hashes[split] = digest(output)

    manifest = {
        "schema_version": 1,
        "purpose": "completion-masked rehearsal of method emission and numerical reasoning",
        "small_model_inputs": "natural language only",
        "sources": {
            "method_train": {"path": str(method_train_path), "sha256": digest(method_train_path)},
            "method_valid": {"path": str(method_valid_path), "sha256": digest(method_valid_path)},
            "numeric_train": {"path": str(numeric_train_path), "sha256": digest(numeric_train_path)},
            "numeric_valid": {"path": str(numeric_valid_path), "sha256": digest(numeric_valid_path)},
        },
        "counts": {
            "train": {"method": len(method_train), "numeric": len(numeric_train), "total": len(splits["train"])},
            "valid": {"method": len(method_valid), "numeric": len(numeric_valid), "total": len(splits["valid"])},
        },
        "selection": {
            "numeric_train_per_family": args.numeric_train_per_family,
            "numeric_valid_per_family": args.numeric_valid_per_family,
            "numeric_families": list(NUMERIC_FAMILIES),
            "order": "sha256 salted by split and ID",
        },
        "output_sha256": output_hashes,
        "train_valid_overlap": 0,
    }
    (args.output / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
