#!/usr/bin/env python3
"""Build reproducible oracle prediction/private batches for ladder preflight."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--targets", type=Path, action="append", required=True)
    parser.add_argument("--verifier", type=Path, action="append", required=True)
    parser.add_argument("--condition", choices=("free", "ordered"), required=True)
    parser.add_argument("--predictions-out", type=Path, required=True)
    parser.add_argument("--private-out", type=Path, required=True)
    args = parser.parse_args()
    if len(args.targets) != len(args.verifier):
        raise ValueError("target and verifier file counts must match")

    targets = [row for path in args.targets for row in read_jsonl(path)]
    private = [row for path in args.verifier for row in read_jsonl(path)]
    if len({row["id"] for row in targets}) != len(targets):
        raise ValueError("duplicate target IDs")
    if len({row["id"] for row in private}) != len(private):
        raise ValueError("duplicate private IDs")
    if {row["id"] for row in targets} != {row["id"] for row in private}:
        raise ValueError("target/private ID mismatch")

    predictions = [
        {"id": row["id"], "response": row[f"target_{args.condition}"]}
        for row in targets
    ]
    write_jsonl(args.predictions_out, predictions)
    write_jsonl(args.private_out, private)
    print(
        json.dumps(
            {
                "condition": args.condition,
                "rows": len(predictions),
                "predictions_out": str(args.predictions_out),
                "private_out": str(args.private_out),
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
