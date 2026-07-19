#!/usr/bin/env python3
"""Build a deterministic, stratified rehearsal mix from two raw data views."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import defaultdict
from pathlib import Path


TRAIN_A = {
    "integer_expression": 100,
    "gcd_bezout": 100,
    "modular_inverse": 150,
    "quadratic_integer_roots": 200,
    "linear_system": 50,
}
TRAIN_B = {
    "integer_expression": 100,
    "gcd_bezout": 150,
    "modular_inverse": 100,
    "quadratic_integer_roots": 50,
    "linear_system": 200,
}
EVAL_EACH = {
    "integer_expression": 20,
    "gcd_bezout": 20,
    "modular_inverse": 20,
    "quadratic_integer_roots": 20,
    "linear_system": 20,
}


def file_hash(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def select(path: Path, counts: dict[str, int], salt: str, source_label: str) -> list[dict]:
    grouped: dict[str, list[dict]] = defaultdict(list)
    for line in path.read_text().splitlines():
        if line.strip():
            row = json.loads(line)
            grouped[row["metadata"]["family"]].append(row)
    selected: list[dict] = []
    for family, count in counts.items():
        ranked = sorted(
            grouped[family],
            key=lambda row: hashlib.sha256(f"{salt}|{row['text']}".encode()).hexdigest(),
        )
        if len(ranked) < count:
            raise ValueError(f"{path} has only {len(ranked)} rows for {family}, need {count}")
        for row in ranked[:count]:
            copied = dict(row)
            copied["metadata"] = {**row["metadata"], "rehearsal_source": source_label}
            selected.append(copied)
    return selected


def render_hash(rows: list[dict]) -> str:
    payload = "".join(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n" for row in rows)
    return hashlib.sha256(payload.encode()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-a", type=Path, required=True)
    parser.add_argument("--source-b", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)

    manifests = {}
    output_hashes = {}
    output_counts = {}
    for split in ("train", "valid", "test"):
        path_a = args.source_a / f"{split}.jsonl"
        path_b = args.source_b / f"{split}.jsonl"
        counts_a = TRAIN_A if split == "train" else EVAL_EACH
        counts_b = TRAIN_B if split == "train" else EVAL_EACH
        rows = select(path_a, counts_a, f"rehearsal-v1|{split}|a", "trace")
        rows.extend(select(path_b, counts_b, f"rehearsal-v1|{split}|b", "state"))
        rows.sort(key=lambda row: hashlib.sha256(f"rehearsal-order|{split}|{row['text']}".encode()).hexdigest())
        target = args.output / f"{split}.jsonl"
        with target.open("w", encoding="utf-8") as handle:
            for row in rows:
                handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
        output_hashes[split] = render_hash(rows)
        output_counts[split] = len(rows)
        manifests[split] = {
            "source_a_sha256": file_hash(path_a),
            "source_b_sha256": file_hash(path_b),
        }

    manifest = {
        "schema_version": 1,
        "purpose": "balanced raw natural-language rehearsal of trace and direct-state representations",
        "formal_data_read": False,
        "chat_template_used": False,
        "sources": {"a": str(args.source_a), "b": str(args.source_b)},
        "source_hashes": manifests,
        "selection": {
            "train_a": TRAIN_A,
            "train_b": TRAIN_B,
            "valid_each": EVAL_EACH,
            "test_each": EVAL_EACH,
        },
        "counts": output_counts,
        "sha256": output_hashes,
    }
    (args.output / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
