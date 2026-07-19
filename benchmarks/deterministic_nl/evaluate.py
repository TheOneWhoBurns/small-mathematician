#!/usr/bin/env python3
"""Evaluate natural-language model responses with exact family verifiers."""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from pathlib import Path
from typing import Any

from benchmark import DATA, evaluate_response, load_instances, write_jsonl


def rate(rows: list[dict[str, Any]], field: str) -> float:
    return sum(bool(row[field]) for row in rows) / len(rows) if rows else 0.0


def summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    grouped: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        grouped[row["family"]].append(row)

    def metrics(group: list[dict[str, Any]]) -> dict[str, Any]:
        certificate_rows = [row for row in group if row["certificate_valid"] is not None]
        return {
            "count": len(group),
            "format_valid_rate": rate(group, "format_valid"),
            "answer_accuracy": rate(group, "answer_correct"),
            "reasoning_present_rate": rate(group, "reasoning_present"),
            "certificate_valid_rate": rate(certificate_rows, "certificate_valid") if certificate_rows else None,
            "strict_pass_rate": rate(group, "strict_pass"),
        }

    per_family = {family: metrics(group) for family, group in sorted(grouped.items())}
    macro_fields = ("format_valid_rate", "answer_accuracy", "reasoning_present_rate", "strict_pass_rate")
    macro = {
        field: sum(family_metrics[field] for family_metrics in per_family.values()) / len(per_family)
        for field in macro_fields
    }
    certificate_values = [
        family_metrics["certificate_valid_rate"]
        for family_metrics in per_family.values()
        if family_metrics["certificate_valid_rate"] is not None
    ]
    macro["certificate_valid_rate"] = (
        sum(certificate_values) / len(certificate_values) if certificate_values else None
    )
    return {
        "overall": metrics(rows),
        "macro_family_average": macro,
        "per_family": per_family,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--split", choices=("dev", "test"), required=True)
    parser.add_argument("--predictions", type=Path, required=True, help="JSONL rows with id and response")
    parser.add_argument("--data-dir", type=Path, default=DATA)
    parser.add_argument("--details-out", type=Path)
    args = parser.parse_args()

    instances = load_instances(args.split, args.data_dir)
    expected = {instance.id: instance for instance in instances}
    predictions: dict[str, str] = {}
    with args.predictions.open(encoding="utf-8") as handle:
        for line_number, line in enumerate(handle, 1):
            if not line.strip():
                continue
            row = json.loads(line)
            if set(("id", "response")) - row.keys():
                raise ValueError(f"prediction line {line_number} needs id and response")
            if row["id"] in predictions:
                raise ValueError(f"duplicate prediction ID {row['id']}")
            predictions[row["id"]] = row["response"]
    unknown = predictions.keys() - expected.keys()
    if unknown:
        raise ValueError(f"unknown prediction IDs: {sorted(unknown)[:3]}")
    details = [evaluate_response(instance, predictions.get(instance.id, "")) for instance in instances]
    report = {
        "split": args.split,
        "predictions_received": len(predictions),
        "instances_expected": len(instances),
        **summarize(details),
    }
    if args.details_out:
        write_jsonl(args.details_out, details)
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
