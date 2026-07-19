#!/usr/bin/env python3
"""Evaluate ordinary-English plan predictions with strict family-specific parsers."""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from pathlib import Path
from typing import Any

from benchmark import DATA, EVAL_SPLITS, SPLIT_COUNTS, evaluate_response, load_instances, write_jsonl


def _mean(rows: list[dict[str, Any]], field: str) -> float:
    return sum(float(row[field]) for row in rows) / len(rows) if rows else 0.0


def summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    grouped: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        grouped[row["family"]].append(row)

    def metrics(group: list[dict[str, Any]]) -> dict[str, Any]:
        return {
            "count": len(group),
            "parse_rate": _mean(group, "parse_valid"),
            "critical_fact_precision": _mean(group, "required_fact_precision"),
            "required_fact_recall": _mean(group, "required_fact_recall"),
            "order_valid_rate": _mean(group, "order_valid"),
            "conclusion_accuracy": _mean(group, "conclusion_correct"),
            "strict_plan_rate": _mean(group, "python_strict"),
        }

    per_family = {family: metrics(group) for family, group in sorted(grouped.items())}
    macro = {key: sum(row[key] for row in per_family.values()) / len(per_family)
             for key in next(iter(per_family.values())) if key != "count"} if per_family else {}
    return {"overall": metrics(rows), "macro_family_average": macro, "per_family": per_family}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--split", choices=("all", "train", *EVAL_SPLITS), required=True)
    parser.add_argument("--condition", choices=("free", "ordered"), required=True)
    parser.add_argument("--predictions", type=Path, required=True, help="JSONL rows with id and natural-language response")
    parser.add_argument("--data-dir", type=Path, default=DATA)
    parser.add_argument("--details-out", type=Path)
    parser.add_argument(
        "--allow-partial",
        action="store_true",
        help="Score only supplied IDs; intended for explicitly labeled diagnostic subsets.",
    )
    args = parser.parse_args()
    selected_splits = tuple(SPLIT_COUNTS) if args.split == "all" else (args.split,)
    instances = [instance for split in selected_splits for instance in load_instances(split, args.data_dir)]
    instances_expected = len(instances)
    expected = {row.id: row for row in instances}
    predictions: dict[str, str] = {}
    with args.predictions.open(encoding="utf-8") as handle:
        for number, line in enumerate(handle, 1):
            if not line.strip():
                continue
            row = json.loads(line)
            if not isinstance(row.get("response"), str) or "id" not in row:
                raise ValueError(f"prediction line {number} needs string id and response")
            if row["id"] in predictions:
                raise ValueError(f"duplicate prediction ID {row['id']}")
            predictions[row["id"]] = row["response"]
    unknown = predictions.keys() - expected.keys()
    if unknown:
        raise ValueError(f"unknown prediction IDs: {sorted(unknown)[:3]}")
    if args.allow_partial:
        instances = [row for row in instances if row.id in predictions]
    details = [evaluate_response(row, predictions.get(row.id, ""), args.condition) for row in instances]
    report = {"split": args.split, "condition": args.condition, "predictions_received": len(predictions),
              "instances_expected": instances_expected,
              "instances_scored": len(instances), "allow_partial": args.allow_partial,
              **summarize(details),
              "per_split": {split: summarize([row for row in details if row["split"] == split])
                            for split in selected_splits}}
    if args.details_out:
        write_jsonl(args.details_out, details)
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
