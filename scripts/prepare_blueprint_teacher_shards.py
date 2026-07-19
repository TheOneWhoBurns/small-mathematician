#!/usr/bin/env python3
"""Prepare deterministic, training-only proof examples for blueprint distillation."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--view", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--rows", type=int, default=60)
    parser.add_argument("--shards", type=int, default=2)
    parser.add_argument("--max-source-tokens", type=int, default=700)
    parser.add_argument("--selection-salt", default="blueprint-pilot-v1")
    parser.add_argument("--exclude-dir", type=Path, action="append")
    args = parser.parse_args()

    if args.rows < 1 or args.shards < 1 or args.rows % args.shards:
        raise ValueError("rows must be positive and divisible by shards")

    source = args.view / "train.jsonl"
    rows = [json.loads(line) for line in source.read_text().splitlines() if line.strip()]
    excluded_ids = {
        row["id"]
        for directory in (args.exclude_dir or [])
        for path in directory.glob("teacher-input-*.jsonl")
        for row in (json.loads(line) for line in path.read_text().splitlines() if line.strip())
    }
    eligible = [
        row
        for row in rows
        if row["metadata"]["tokens"] <= args.max_source_tokens
        and row["metadata"]["id"] not in excluded_ids
    ]
    eligible.sort(
        key=lambda row: hashlib.sha256(
            f"{args.selection_salt}|{row['metadata']['id']}".encode()
        ).hexdigest()
    )
    selected = eligible[: args.rows]
    if len(selected) != args.rows:
        raise ValueError(f"needed {args.rows} eligible rows, found {len(selected)}")

    args.output_dir.mkdir(parents=True, exist_ok=True)
    per_shard = args.rows // args.shards
    shard_hashes: dict[str, str] = {}
    for shard_index in range(args.shards):
        path = args.output_dir / f"teacher-input-{shard_index:02d}.jsonl"
        start = shard_index * per_shard
        with path.open("w", encoding="utf-8") as handle:
            for row in selected[start : start + per_shard]:
                handle.write(
                    json.dumps(
                        {
                            "id": row["metadata"]["id"],
                            "family_id": row["metadata"]["family_id"],
                            "problem": row["prompt"],
                            "reference_proof": row["completion"],
                        },
                        ensure_ascii=False,
                        sort_keys=True,
                    )
                    + "\n"
                )
        shard_hashes[path.name] = sha256(path)

    manifest = {
        "schema_version": 1,
        "selection": f"lowest sha256('{args.selection_salt}|' + training id)",
        "selection_salt": args.selection_salt,
        "excluded_ids": len(excluded_ids),
        "source": str(source),
        "source_sha256": sha256(source),
        "training_split_only": True,
        "rows": args.rows,
        "shards": args.shards,
        "max_source_tokens": args.max_source_tokens,
        "shard_sha256": shard_hashes,
    }
    (args.output_dir / "manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
