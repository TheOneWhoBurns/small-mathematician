#!/usr/bin/env python3
"""Strictly evaluate divisibility follow-ups after accepted gcd claims."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


def load(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--predictions", type=Path, required=True)
    parser.add_argument("--verifier", type=Path, required=True)
    parser.add_argument("--details", type=Path, required=True)
    args = parser.parse_args()
    predictions = {row["id"]: " ".join(row["response"].strip().split()) for row in load(args.predictions)}
    expected = {row["id"]: row for row in load(args.verifier)}
    details = []
    for identifier, row in expected.items():
        response = predictions[identifier]
        params = row["parameters"]
        match = re.fullmatch(r"(?:It|-?\d+) (does|does not) divide (-?\d+)\.?", response)
        relation = "does" if params["solvable"] else "does not"
        semantic = bool(match and match.group(1) == relation and int(match.group(2)) == params["c"])
        details.append({"id": identifier, "response": response, "expected": row["expected"], "semantic": semantic})
    args.details.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in details), encoding="utf-8")
    passed = sum(int(row["semantic"]) for row in details)
    print(json.dumps({"stage1_gcd_accepted": len(details), "stage2_accepted": passed, "end_to_end_coverage_over_original_8": passed / 8}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
