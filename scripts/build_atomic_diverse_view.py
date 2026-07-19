#!/usr/bin/env python3
"""Create a declared paraphrase-development/holdout split for atomic claims."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


def load_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows), encoding="utf-8")


def index(row: dict) -> int:
    match = re.search(r"-(\d{3})-[^-]+$", row["id"])
    if not match:
        raise ValueError(row["id"])
    return int(match.group(1))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--atomic-dir", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--development-repetitions", type=int, default=5)
    parser.add_argument("--family")
    args = parser.parse_args()

    canonical = load_jsonl(args.atomic_dir / "training" / "train.jsonl")
    valid = load_jsonl(args.atomic_dir / "training" / "valid.jsonl")
    paraphrase = load_jsonl(args.atomic_dir / "paraphrase.verifier.jsonl")
    if args.family:
        canonical = [row for row in canonical if row.get("metadata", {}).get("family") == args.family]
        valid = [row for row in valid if row.get("metadata", {}).get("family") == args.family]
        paraphrase = [row for row in paraphrase if row["family"] == args.family]
    development = [row for row in paraphrase if index(row) < 8]
    holdout = [row for row in paraphrase if index(row) >= 8]
    expected = 8 if args.family else 16
    if len(development) != expected or len(holdout) != expected:
        raise ValueError((len(development), len(holdout)))

    dev_training = [
        {"prompt": row["prompt"], "completion": row["completion"], "metadata": {"id": row["id"], "family": row["family"]}}
        for row in development
    ]
    train = canonical + dev_training * args.development_repetitions
    write_jsonl(args.output_dir / "training" / "train.jsonl", train)
    write_jsonl(args.output_dir / "training" / "valid.jsonl", valid)
    write_jsonl(args.output_dir / "holdout.prompts.jsonl", [{"id": row["id"], "family": row["family"], "prompt": row["prompt"]} for row in holdout])
    write_jsonl(args.output_dir / "holdout.verifier.jsonl", holdout)
    write_jsonl(args.output_dir / "development.verifier.jsonl", development)
    print(json.dumps({"canonical": len(canonical), "development": len(development), "development_repetitions": args.development_repetitions, "train": len(train), "holdout": len(holdout)}, sort_keys=True))


if __name__ == "__main__":
    main()
