#!/usr/bin/env python3
"""Analyze paired trace capability by oracle Euclidean-chain length."""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from pathlib import Path

from compare_atomic_evaluations import exact_two_sided_mcnemar
from evaluate_diophantine_traces import STEP


def load(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def bucket(length: int) -> str:
    if length <= 3:
        return "1-3"
    if length <= 5:
        return "4-5"
    return "6+"


def summarize(rows: list[dict], metric: str) -> dict:
    count = len(rows)
    before = sum(int(row["baseline"][metric]) for row in rows)
    after = sum(int(row["candidate"][metric]) for row in rows)
    helped = sum(int(not row["baseline"][metric] and row["candidate"][metric]) for row in rows)
    harmed = sum(int(row["baseline"][metric] and not row["candidate"][metric]) for row in rows)
    return {
        "count": count,
        "baseline": before,
        "baseline_rate": before / count,
        "candidate": after,
        "candidate_rate": after / count,
        "helped": helped,
        "harmed": harmed,
        "mcnemar_exact_two_sided_p": exact_two_sided_mcnemar(helped, harmed),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--verifier", type=Path, required=True)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    verifier = {row["id"]: row for row in load(args.verifier)}
    baseline = {row["id"]: row for row in load(args.baseline)}
    candidate = {row["id"]: row for row in load(args.candidate)}
    if not (verifier.keys() == baseline.keys() == candidate.keys()):
        raise ValueError("IDs do not match")
    grouped: dict[str, list[dict]] = defaultdict(list)
    for identifier, private in verifier.items():
        length = len(STEP.findall(private["expected"]))
        row = {"length": length, "baseline": baseline[identifier], "candidate": candidate[identifier]}
        grouped[bucket(length)].append(row)
    report = {
        label: {
            "complete": summarize(rows, "semantic"),
            "core": summarize(rows, "trace_valid"),
            "mean_steps": sum(row["length"] for row in rows) / len(rows),
        }
        for label, rows in sorted(grouped.items())
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
