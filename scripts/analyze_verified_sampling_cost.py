#!/usr/bin/env python3
"""Measure verifier-triggered early-stop cost for every candidate ordering."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path


def load(path: Path) -> dict[str, bool]:
    rows: dict[str, bool] = {}
    with path.open() as handle:
        for line in handle:
            row = json.loads(line)
            rows[row["id"]] = bool(row["trace_valid"])
    return rows


def score(order: tuple[int, ...], arms: list[dict[str, bool]], ids: list[str]) -> dict:
    prefix_coverage: list[int] = []
    covered: set[str] = set()
    for arm in order:
        covered.update(item_id for item_id in ids if arms[arm][item_id])
        prefix_coverage.append(len(covered))
    generated = [next((rank + 1 for rank, arm in enumerate(order) if arms[arm][item_id]), len(order)) for item_id in ids]
    return {
        "order": list(order),
        "prefix_coverage": prefix_coverage,
        "mean_candidates_with_early_stop": sum(generated) / len(generated),
        "relative_to_exhaustive": sum(generated) / (len(generated) * len(order)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--arm", action="append", required=True)
    parser.add_argument("--output")
    args = parser.parse_args()
    arms = [load(Path(path)) for path in args.arm]
    ids = sorted(arms[0])
    if any(sorted(arm) != ids for arm in arms[1:]):
        raise SystemExit("candidate ID sets differ")
    scores = [score(order, arms, ids) for order in itertools.permutations(range(len(arms)))]
    scores.sort(key=lambda row: (row["mean_candidates_with_early_stop"], row["order"]))
    registered = score(tuple(range(len(arms))), arms, ids)
    standalone = [sum(arm[item_id] for item_id in ids) for arm in arms]
    report = json.dumps({"count": len(ids), "standalone_valid": standalone, "registered": registered, "best": scores[0], "all_orders": scores}, indent=2) + "\n"
    if args.output:
        Path(args.output).write_text(report)
    print(report, end="")


if __name__ == "__main__":
    main()
