#!/usr/bin/env python3
"""Build sealed gcd-only evaluation prompts from atomic verifier rows."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def load(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def write(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--verifier", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    rows = load(args.verifier)
    prompts, verifier = [], []
    for row in rows:
        prefix = row["prompt"].split("Task:", 1)[0]
        prompts.append({"id": row["id"], "family": row["family"], "prompt": prefix + "Task: State exactly one sentence giving the greatest common divisor. Do not add any other claim.\nClaim: "})
        verifier.append({"id": row["id"], "expected_gcd": row["parameters"]["gcd"], "parameters": row["parameters"]})
    write(args.output_dir / "prompts.jsonl", prompts)
    write(args.output_dir / "verifier.jsonl", verifier)
    print(json.dumps({"count": len(rows)}))


if __name__ == "__main__":
    main()
