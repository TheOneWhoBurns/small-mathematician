#!/usr/bin/env python3
"""Calibrate a no-false-accept confidence threshold, then apply it once."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def load(path: Path) -> dict[str, dict]:
    return {row["id"]: row for row in (json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip())}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--calibration-scores", type=Path, required=True)
    parser.add_argument("--calibration-details", type=Path, required=True)
    parser.add_argument("--test-scores", type=Path, required=True)
    parser.add_argument("--test-details", type=Path, required=True)
    args = parser.parse_args()

    cal_scores, cal_details = load(args.calibration_scores), load(args.calibration_details)
    test_scores, test_details = load(args.test_scores), load(args.test_details)
    thresholds = sorted({row["mean_log_probability"] for row in cal_scores.values()}, reverse=True)
    candidates = []
    for threshold in thresholds:
        accepted = [identifier for identifier, row in cal_scores.items() if row["mean_log_probability"] >= threshold]
        correct = sum(int(cal_details[identifier]["semantic"]) for identifier in accepted)
        if correct == len(accepted):
            candidates.append((len(accepted), threshold))
    accepted_count, threshold = max(candidates, default=(0, float("inf")))
    test_accepted = [identifier for identifier, row in test_scores.items() if row["mean_log_probability"] >= threshold]
    test_correct = sum(int(test_details[identifier]["semantic"]) for identifier in test_accepted)
    report = {
        "selection_contract": "highest-coverage mean-log-probability threshold with zero calibration false accepts",
        "threshold": threshold,
        "calibration": {"count": len(cal_scores), "accepted": accepted_count, "precision": 1.0 if accepted_count else None, "coverage": accepted_count / len(cal_scores)},
        "test": {"count": len(test_scores), "accepted": len(test_accepted), "correct": test_correct, "precision": test_correct / len(test_accepted) if test_accepted else None, "coverage": len(test_accepted) / len(test_scores)},
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
