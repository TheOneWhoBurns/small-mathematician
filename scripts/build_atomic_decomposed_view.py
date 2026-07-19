#!/usr/bin/env python3
"""Expand joint Diophantine atomic data into a verified two-step curriculum."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


JOINT = re.compile(r"The greatest common divisor is (-?\d+), and it (does|does not) divide (-?\d+)\.")


def load(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def write(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows), encoding="utf-8")


def variants(row: dict) -> list[dict]:
    match = JOINT.fullmatch(row["completion"])
    if not match:
        raise ValueError(row["completion"])
    gcd_value, relation, c = match.groups()
    prefix = row["prompt"].split("Task:", 1)[0]
    metadata = row.get("metadata", {})
    gcd_row = {
        "prompt": prefix + "Task: State exactly one sentence giving the greatest common divisor. Do not add any other claim.\nClaim: ",
        "completion": f"The greatest common divisor is {gcd_value}.",
        "metadata": {**metadata, "stage": "gcd"},
    }
    relation_row = {
        "prompt": prefix + f"Verified intermediate claim: The greatest common divisor is {gcd_value}.\nTask: State exactly one sentence saying whether {gcd_value} divides {c}. Do not add any other claim.\nClaim: ",
        "completion": f"It {relation} divide {c}.",
        "metadata": {**metadata, "stage": "divisibility"},
    }
    return [row, gcd_row, relation_row]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-training", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    counts = {}
    for split in ("train", "valid"):
        source = load(args.source_training / f"{split}.jsonl")
        expanded = [variant for row in source for variant in variants(row)]
        write(args.output_dir / f"{split}.jsonl", expanded)
        counts[split] = {"source": len(source), "expanded": len(expanded)}
    print(json.dumps(counts, sort_keys=True))


if __name__ == "__main__":
    main()
