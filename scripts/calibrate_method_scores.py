#!/usr/bin/env python3
"""Diagnose fixed candidate bias in natural-language method likelihoods.

The reference set is used only to estimate one mean score per candidate method.
No reference labels are consulted.  Subtracting those means is therefore a
label-prior diagnostic, not a fitted classifier.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from pathlib import Path


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def evaluate(rows: list[dict], offsets: dict[str, float]) -> dict:
    confusion: Counter[tuple[str, str]] = Counter()
    predictions: list[dict] = []
    pair_correct: dict[str, list[bool]] = defaultdict(list)
    for row in rows:
        adjusted = {
            route: score - offsets.get(route, 0.0)
            for route, score in row["mean_log_probability"].items()
        }
        predicted = max(adjusted, key=adjusted.get)
        expected = row["expected_route"]
        correct = predicted == expected
        confusion[(expected, predicted)] += 1
        if row.get("pair_id"):
            pair_correct[row["pair_id"]].append(correct)
        predictions.append(
            {
                "id": row["id"],
                "expected_route": expected,
                "predicted_route": predicted,
                "correct": correct,
                "adjusted_scores": adjusted,
                "pair_id": row.get("pair_id"),
            }
        )
    return {
        "accuracy": sum(row["correct"] for row in predictions) / len(predictions),
        "pair_accuracy": (
            sum(len(values) == 2 and all(values) for values in pair_correct.values())
            / len(pair_correct)
            if pair_correct
            else None
        ),
        "prediction_counts": dict(sorted(Counter(row["predicted_route"] for row in predictions).items())),
        "confusion": [
            {"expected": expected, "predicted": predicted, "count": count}
            for (expected, predicted), count in sorted(confusion.items())
        ],
        "predictions": predictions,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--reference", type=Path, required=True)
    parser.add_argument("--evaluation", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    reference = read_jsonl(args.reference)
    evaluation = read_jsonl(args.evaluation)
    routes = sorted(reference[0]["mean_log_probability"])
    offsets = {
        route: sum(row["mean_log_probability"][route] for row in reference) / len(reference)
        for route in routes
    }
    report = {
        "schema_version": 1,
        "purpose": "diagnose candidate-method score priors; not a fitted task classifier",
        "reference": str(args.reference),
        "evaluation": str(args.evaluation),
        "reference_labels_used": False,
        "candidate_mean_offsets": offsets,
        "raw": evaluate(evaluation, {}),
        "reference_mean_centered": evaluate(evaluation, offsets),
    }
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    summary = {key: value for key, value in report.items() if key not in {"raw", "reference_mean_centered"}}
    summary["raw"] = {key: value for key, value in report["raw"].items() if key != "predictions"}
    summary["reference_mean_centered"] = {
        key: value for key, value in report["reference_mean_centered"].items() if key != "predictions"
    }
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
