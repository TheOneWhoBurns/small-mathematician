#!/usr/bin/env python3
"""Build frozen-readout views for verified-gcd divisibility decisions."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


def load(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def write(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows), encoding="utf-8")


def training_rows(path: Path) -> list[dict]:
    rows = []
    for row in load(path):
        if row.get("metadata", {}).get("stage") != "divisibility":
            continue
        label = "does_not_divide" if "does not divide" in row["completion"] else "does_divide"
        rows.append({"id": row["metadata"].get("id", str(len(rows))), "prompt": row["prompt"], "family": label})
    return rows


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--training-dir", type=Path, required=True)
    parser.add_argument("--holdout-verifier", type=Path, required=True)
    parser.add_argument("--development-verifier", type=Path)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    train = training_rows(args.training_dir / "train.jsonl")
    train = [row for row in train if "-train-" in row["id"]]

    def verifier_rows(path: Path) -> list[dict]:
        output = []
        for row in load(path):
            params = row["parameters"]
            gcd_value, c = params["gcd"], params["c"]
            prefix = row["prompt"].split("Task:", 1)[0]
            prompt = prefix + f"Verified intermediate claim: The greatest common divisor is {gcd_value}.\nTask: State exactly one sentence saying whether {gcd_value} divides {c}. Do not add any other claim.\nClaim: "
            label = "does_divide" if params["solvable"] else "does_not_divide"
            output.append({"id": row["id"], "prompt": prompt, "family": label})
        return output

    valid = verifier_rows(args.development_verifier) if args.development_verifier else training_rows(args.training_dir / "valid.jsonl")
    test = verifier_rows(args.holdout_verifier)
    write(args.output_dir / "train.jsonl", train)
    write(args.output_dir / "valid.jsonl", valid)
    write(args.output_dir / "holdout.jsonl", test)
    print(json.dumps({"train": len(train), "valid": len(valid), "holdout": len(test)}))


if __name__ == "__main__":
    main()
