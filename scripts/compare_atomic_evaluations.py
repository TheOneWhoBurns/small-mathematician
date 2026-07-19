#!/usr/bin/env python3
"""Paired comparison of two sealed atomic-claim evaluation detail files."""

from __future__ import annotations

import argparse
import json
import math
from collections import Counter
from pathlib import Path


def load_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def exact_two_sided_mcnemar(helped: int, harmed: int) -> float:
    discordant = helped + harmed
    if discordant == 0:
        return 1.0
    tail = sum(math.comb(discordant, k) for k in range(min(helped, harmed) + 1)) / (2**discordant)
    return min(1.0, 2.0 * tail)


def summarize(rows: list[dict]) -> dict:
    baseline = sum(int(row["baseline_semantic"]) for row in rows)
    candidate = sum(int(row["candidate_semantic"]) for row in rows)
    helped = sum(int(not row["baseline_semantic"] and row["candidate_semantic"]) for row in rows)
    harmed = sum(int(row["baseline_semantic"] and not row["candidate_semantic"]) for row in rows)
    count = len(rows)
    return {
        "count": count,
        "baseline_semantic": baseline,
        "baseline_rate": baseline / count,
        "candidate_semantic": candidate,
        "candidate_rate": candidate / count,
        "delta": (candidate - baseline) / count,
        "helped": helped,
        "harmed": harmed,
        "mcnemar_exact_two_sided_p": exact_two_sided_mcnemar(helped, harmed),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--metric", default="semantic")
    args = parser.parse_args()

    baseline = {row["id"]: row for row in load_jsonl(args.baseline)}
    candidate = {row["id"]: row for row in load_jsonl(args.candidate)}
    if baseline.keys() != candidate.keys():
        raise ValueError("baseline and candidate IDs do not match")

    paired = []
    for problem_id in baseline:
        before = baseline[problem_id]
        after = candidate[problem_id]
        if before.get("surface", "unspecified") != after.get("surface", "unspecified"):
            raise ValueError(f"surface mismatch for {problem_id}")
        paired.append(
            {
                "id": problem_id,
                "surface": before.get("surface", "unspecified"),
                "baseline_semantic": bool(before[args.metric]),
                "candidate_semantic": bool(after[args.metric]),
            }
        )

    surfaces = Counter(row["surface"] for row in paired)
    report = {
        "metric": args.metric,
        "overall": summarize(paired),
        "per_surface": {
            surface: summarize([row for row in paired if row["surface"] == surface])
            for surface in sorted(surfaces)
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
