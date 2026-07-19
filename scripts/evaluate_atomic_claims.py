#!/usr/bin/env python3
"""Strictly score a sealed atomic-claim response file."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from collections import Counter
from pathlib import Path


def load_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def normalize(text: str) -> str:
    return " ".join(text.strip().split())


def semantically_valid(response: str, row: dict) -> bool:
    params = row["parameters"]
    if row["family"] == "polynomial_value_obstruction":
        match = re.fullmatch(
            r"The input difference is (-?\d+),? and the proposed value difference is (-?\d+)\.?",
            response,
        )
        return bool(
            match
            and int(match.group(1)) == params["input_difference"]
            and int(match.group(2)) == params["value_difference"]
        )
    match = re.fullmatch(
        r"The greatest common divisor is (-?\d+),? and it (does|does not) divide (-?\d+)\.?",
        response,
    )
    expected_relation = "does" if params["solvable"] else "does not"
    return bool(
        match
        and int(match.group(1)) == params["gcd"]
        and match.group(2) == expected_relation
        and int(match.group(3)) == params["c"]
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--predictions", type=Path, required=True)
    parser.add_argument("--verifier", type=Path, required=True)
    parser.add_argument("--details", type=Path, required=True)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--allow-subset", action="store_true")
    args = parser.parse_args()

    predictions = {row["id"]: row["response"] for row in load_jsonl(args.predictions)}
    expected = load_jsonl(args.verifier)
    if args.allow_subset:
        expected = [row for row in expected if row["id"] in predictions]
    if set(predictions) != {row["id"] for row in expected}:
        raise ValueError("prediction IDs do not exactly match verifier IDs")
    details = []
    for row in expected:
        response = normalize(predictions[row["id"]])
        target = normalize(row["expected"])
        details.append(
            {
                "id": row["id"],
                "family": row["family"],
                "surface": row.get("surface", "unspecified"),
                "response": response,
                "expected": target,
                "strict": response == target,
                "semantic": semantically_valid(response, row),
            }
        )
    args.details.parent.mkdir(parents=True, exist_ok=True)
    args.details.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in details), encoding="utf-8")
    by_family = Counter()
    semantic_by_family = Counter()
    totals = Counter()
    by_surface = Counter()
    semantic_by_surface = Counter()
    surface_totals = Counter()
    for row in details:
        totals[row["family"]] += 1
        by_family[row["family"]] += int(row["strict"])
        semantic_by_family[row["family"]] += int(row["semantic"])
        surface_totals[row["surface"]] += 1
        by_surface[row["surface"]] += int(row["strict"])
        semantic_by_surface[row["surface"]] += int(row["semantic"])
    report = {
        "count": len(details),
        "strict": sum(int(row["strict"]) for row in details),
        "strict_rate": sum(int(row["strict"]) for row in details) / len(details),
        "semantic": sum(int(row["semantic"]) for row in details),
        "semantic_rate": sum(int(row["semantic"]) for row in details) / len(details),
        "per_family": {family: {"strict": by_family[family], "strict_rate": by_family[family] / totals[family], "semantic": semantic_by_family[family], "semantic_rate": semantic_by_family[family] / totals[family], "count": totals[family]} for family in sorted(totals)},
        "per_surface": {surface: {"strict": by_surface[surface], "strict_rate": by_surface[surface] / surface_totals[surface], "semantic": semantic_by_surface[surface], "semantic_rate": semantic_by_surface[surface] / surface_totals[surface], "count": surface_totals[surface]} for surface in sorted(surface_totals)},
        "predictions_sha256": sha256(args.predictions),
        "verifier_sha256": sha256(args.verifier),
    }
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
