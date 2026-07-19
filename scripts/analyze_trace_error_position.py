#!/usr/bin/env python3
"""Locate the first incorrect Euclidean step in free-running traces."""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter, defaultdict
from pathlib import Path


STEP = re.compile(r"Euclidean step: (-?\d+) = (-?\d+) times (-?\d+) plus (-?\d+)\.")


def load_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def oracle_steps(a: int, b: int) -> list[tuple[int, int, int, int]]:
    dividend, divisor = max(a, b), min(a, b)
    steps = []
    while divisor:
        quotient, remainder = divmod(dividend, divisor)
        steps.append((dividend, quotient, divisor, remainder))
        dividend, divisor = divisor, remainder
    return steps


def parsed_steps(response: str) -> list[tuple[int, int, int, int]]:
    return [tuple(map(int, match.groups())) for match in STEP.finditer(response)]


def summarize(predictions: Path, verifier: Path) -> tuple[dict, list[dict]]:
    predicted = {row["id"]: row["response"] for row in load_jsonl(predictions)}
    expected = load_jsonl(verifier)
    if predicted.keys() != {row["id"] for row in expected}:
        raise ValueError("prediction IDs do not match verifier IDs")

    first_error = Counter()
    expected_lengths = Counter()
    parsed_lengths = Counter()
    prefix_exact = Counter()
    next_exact = Counter()
    opportunities = Counter()
    by_surface = defaultdict(lambda: Counter(count=0, first_exact=0, all_steps_exact=0))
    details = []

    for row in expected:
        oracle = oracle_steps(row["parameters"]["a"], row["parameters"]["b"])
        actual = parsed_steps(predicted[row["id"]])
        common = 0
        for got, want in zip(actual, oracle):
            if got != want:
                break
            common += 1
        error = "complete" if actual == oracle else str(common + 1)
        details.append(
            {
                "id": row["id"],
                "surface": row.get("surface", "unspecified"),
                "first_step_exact": common >= 1,
                "common_exact_prefix": common,
                "expected_steps": len(oracle),
                "parsed_steps": len(actual),
                "all_steps_exact": actual == oracle,
            }
        )
        first_error[error] += 1
        expected_lengths[len(oracle)] += 1
        parsed_lengths[len(actual)] += 1
        surface = row.get("surface", "unspecified")
        by_surface[surface]["count"] += 1
        by_surface[surface]["first_exact"] += int(common >= 1)
        by_surface[surface]["all_steps_exact"] += int(actual == oracle)
        for index in range(len(oracle)):
            opportunities[index + 1] += int(common >= index)
            prefix_exact[index] += int(common >= index)
            next_exact[index + 1] += int(common >= index + 1)

    transitions = {}
    for step in sorted(opportunities):
        denom = opportunities[step]
        transitions[str(step)] = {
            "prefix_opportunities": denom,
            "next_exact": next_exact[step],
            "conditional_rate": next_exact[step] / denom if denom else None,
        }
    surfaces = {}
    for surface, values in sorted(by_surface.items()):
        count = values["count"]
        surfaces[surface] = {
            **values,
            "first_exact_rate": values["first_exact"] / count,
            "all_steps_exact_rate": values["all_steps_exact"] / count,
        }
    return {
        "count": len(expected),
        "first_error_step": dict(sorted(first_error.items())),
        "expected_step_lengths": dict(sorted(expected_lengths.items())),
        "parsed_step_lengths": dict(sorted(parsed_lengths.items())),
        "conditional_transition_accuracy": transitions,
        "per_surface": surfaces,
    }, details


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--predictions", type=Path, required=True)
    parser.add_argument("--verifier", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--details", type=Path)
    args = parser.parse_args()
    report, details = summarize(args.predictions, args.verifier)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.details:
        args.details.parent.mkdir(parents=True, exist_ok=True)
        args.details.write_text(
            "".join(json.dumps(row, sort_keys=True) + "\n" for row in details),
            encoding="utf-8",
        )
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
