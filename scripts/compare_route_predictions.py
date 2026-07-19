#!/usr/bin/env python3
"""Paired comparison for two route predictors on identical matched pairs."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import random
from collections import Counter, defaultdict
from pathlib import Path


def read(path: Path) -> dict[str, dict]:
    rows = [json.loads(line) for line in path.read_text().splitlines() if line.strip()]
    return {row["id"]: row for row in rows}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exact_mcnemar(helped: int, harmed: int) -> float:
    discordant = helped + harmed
    if discordant == 0:
        return 1.0
    tail = sum(math.comb(discordant, index) for index in range(min(helped, harmed) + 1))
    return min(1.0, 2.0 * tail / (2**discordant))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--bootstrap-samples", type=int, default=10000)
    parser.add_argument("--seed", type=int, default=20260719)
    args = parser.parse_args()

    candidate = read(args.candidate)
    baseline = read(args.baseline)
    if candidate.keys() != baseline.keys():
        raise ValueError("prediction IDs differ")
    rows = []
    by_pair: dict[str, list[dict]] = defaultdict(list)
    for example_id in sorted(candidate):
        left, right = candidate[example_id], baseline[example_id]
        if left["expected_route"] != right["expected_route"] or left.get("pair_id") != right.get("pair_id"):
            raise ValueError(f"gold or pair mismatch for {example_id}")
        row = {
            "id": example_id,
            "family": left["expected_route"],
            "pair_id": left.get("pair_id"),
            "candidate_correct": bool(left["correct"]),
            "baseline_correct": bool(right["correct"]),
        }
        rows.append(row)
        by_pair[row["pair_id"]].append(row)
    if any(len(group) != 2 for group in by_pair.values()):
        raise ValueError("every pair must contain two rows")

    helped = sum(row["candidate_correct"] and not row["baseline_correct"] for row in rows)
    harmed = sum(row["baseline_correct"] and not row["candidate_correct"] for row in rows)
    candidate_accuracy = sum(row["candidate_correct"] for row in rows) / len(rows)
    baseline_accuracy = sum(row["baseline_correct"] for row in rows) / len(rows)
    rng = random.Random(args.seed)
    pairs = sorted(by_pair)
    draws = []
    for _ in range(args.bootstrap_samples):
        sample = [by_pair[pairs[rng.randrange(len(pairs))]] for _ in pairs]
        flat = [row for pair in sample for row in pair]
        draws.append(
            sum(row["candidate_correct"] - row["baseline_correct"] for row in flat) / len(flat)
        )
    draws.sort()
    per_family = {}
    for family in sorted({row["family"] for row in rows}):
        group = [row for row in rows if row["family"] == family]
        per_family[family] = {
            "count": len(group),
            "candidate_correct": sum(row["candidate_correct"] for row in group),
            "baseline_correct": sum(row["baseline_correct"] for row in group),
        }
    report = {
        "schema_version": 1,
        "candidate": {"path": str(args.candidate), "sha256": digest(args.candidate)},
        "baseline": {"path": str(args.baseline), "sha256": digest(args.baseline)},
        "count": len(rows),
        "pairs": len(pairs),
        "candidate_accuracy": candidate_accuracy,
        "baseline_accuracy": baseline_accuracy,
        "difference_percentage_points": 100 * (candidate_accuracy - baseline_accuracy),
        "helped": helped,
        "harmed": harmed,
        "tied_both_correct": sum(row["candidate_correct"] and row["baseline_correct"] for row in rows),
        "tied_both_wrong": sum(not row["candidate_correct"] and not row["baseline_correct"] for row in rows),
        "exact_mcnemar_two_sided_p": exact_mcnemar(helped, harmed),
        "pair_cluster_bootstrap_difference_95pct_pp": [
            100 * draws[int(0.025 * len(draws))],
            100 * draws[int(0.975 * len(draws))],
        ],
        "bootstrap_samples": args.bootstrap_samples,
        "bootstrap_seed": args.seed,
        "per_family": per_family,
    }
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
