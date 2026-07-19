#!/usr/bin/env python3
"""Build divisibility follow-ups only from verifier-accepted model gcd claims."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


PATTERN = re.compile(r"The greatest common divisor is (-?\d+)(?:,? and it (?:does|does not) divide (-?\d+))?\.?$")


def load(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def write(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--predictions", type=Path, required=True)
    parser.add_argument("--prompts", type=Path, required=True)
    parser.add_argument("--verifier", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    predictions = {row["id"]: row["response"] for row in load(args.predictions)}
    prompts = {row["id"]: row["prompt"] for row in load(args.prompts)}
    private = {row["id"]: row for row in load(args.verifier)}
    prompt_rows, verifier_rows = [], []
    for identifier, response in predictions.items():
        match = PATTERN.fullmatch(" ".join(response.strip().split()))
        if not match:
            continue
        gcd_claim = int(match.group(1))
        params = private[identifier]["parameters"]
        if gcd_claim != params["gcd"]:
            continue
        c = params["c"]
        prefix = prompts[identifier].split("Task:", 1)[0]
        prompt = (
            prefix
            + f"Verified intermediate claim: The greatest common divisor is {gcd_claim}.\n"
            + f"Task: State exactly one sentence saying whether {gcd_claim} divides {c}. Do not add any other claim.\n"
            + "Claim: "
        )
        relation = "does" if params["solvable"] else "does not"
        expected = f"It {relation} divide {c}."
        prompt_rows.append({"id": identifier, "family": "diophantine_solvability", "prompt": prompt})
        verifier_rows.append({"id": identifier, "expected": expected, "parameters": params})
    write(args.output_dir / "prompts.jsonl", prompt_rows)
    write(args.output_dir / "verifier.jsonl", verifier_rows)
    print(json.dumps({"stage1_prompts": len(predictions), "gcd_accepted": len(prompt_rows)}))


if __name__ == "__main__":
    main()
