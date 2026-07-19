#!/usr/bin/env python3
"""Evaluate exact ordinary-English concept selection without grading prose style."""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--prompts", type=Path, required=True)
    parser.add_argument("--predictions", type=Path, required=True)
    parser.add_argument("--details-out", type=Path)
    args = parser.parse_args()

    manifest = json.loads(args.manifest.read_text())
    markers: dict[str, str] = manifest["markers"]
    expected = {row["id"]: row for row in read_jsonl(args.prompts)}
    predictions = {row["id"]: row["response"] for row in read_jsonl(args.predictions)}
    if predictions.keys() != expected.keys():
        raise ValueError("prediction IDs must exactly equal prompt IDs")

    details: list[dict] = []
    confusion: Counter[tuple[str, str]] = Counter()
    for example_id, row in expected.items():
        response = predictions[example_id]
        matched = [family for family, marker in markers.items() if marker in response.lower()]
        predicted = matched[0] if len(matched) == 1 else "ambiguous_or_missing"
        correct = predicted == row["family"]
        confusion[(row["family"], predicted)] += 1
        details.append(
            {
                "id": example_id,
                "family": row["family"],
                "predicted_family": predicted,
                "matched_markers": matched,
                "correct": correct,
                "response": response,
            }
        )
    if args.details_out:
        with args.details_out.open("w", encoding="utf-8") as handle:
            for row in details:
                handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
    per_family = {
        family: {
            "count": sum(row["family"] == family for row in details),
            "accuracy": sum(row["family"] == family and row["correct"] for row in details)
            / sum(row["family"] == family for row in details),
        }
        for family in sorted(markers)
    }
    report = {
        "count": len(details),
        "accuracy": sum(row["correct"] for row in details) / len(details),
        "ambiguous_or_missing": sum(row["predicted_family"] == "ambiguous_or_missing" for row in details),
        "per_family": per_family,
        "confusion": [
            {"expected": expected_family, "predicted": predicted_family, "count": count}
            for (expected_family, predicted_family), count in sorted(confusion.items())
        ],
        "interpretation": "Correct routing permits the fixed executor to instantiate and certify; it is not itself a generated proof.",
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
