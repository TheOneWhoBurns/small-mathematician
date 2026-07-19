#!/usr/bin/env python3
"""Strictly verify generated single-step Euclidean divisions."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from collections import defaultdict
from pathlib import Path


PATTERN = re.compile(r"^\s*Euclidean step:\s*(-?\d+)\s*=\s*(-?\d+)\s+times\s+(-?\d+)\s+plus\s+(-?\d+)\.\s*$")


def read(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--predictions", type=Path, required=True)
    parser.add_argument("--verifier", type=Path, required=True)
    parser.add_argument("--details", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()

    predictions = {row["id"]: row for row in read(args.predictions)}
    truth = read(args.verifier)
    if set(predictions) != {row["id"] for row in truth}:
        raise ValueError("prediction and verifier IDs differ")
    details = []
    per_surface: dict[str, dict[str, int]] = defaultdict(lambda: {"count": 0, "valid": 0})
    for row in truth:
        prediction_row = predictions[row["id"]]
        prediction = prediction_row.get("prediction", prediction_row.get("response", ""))
        match = PATTERN.fullmatch(prediction)
        expected = row["parameters"]
        parsed = tuple(map(int, match.groups())) if match else None
        valid = parsed == (
            expected["dividend"],
            expected["quotient"],
            expected["divisor"],
            expected["remainder"],
        )
        surface = row["surface"]
        per_surface[surface]["count"] += 1
        per_surface[surface]["valid"] += int(valid)
        details.append({"id": row["id"], "surface": surface, "prediction": prediction, "parsed": parsed, "valid": valid})
    args.details.parent.mkdir(parents=True, exist_ok=True)
    write = lambda path, rows: path.write_text("".join(json.dumps(value, sort_keys=True) + "\n" for value in rows), encoding="utf-8")
    write(args.details, details)
    valid = sum(row["valid"] for row in details)
    report = {
        "count": len(details),
        "valid": valid,
        "valid_rate": valid / len(details),
        "per_surface": {surface: {**counts, "valid_rate": counts["valid"] / counts["count"]} for surface, counts in sorted(per_surface.items())},
        "predictions_sha256": sha256(args.predictions),
        "verifier_sha256": sha256(args.verifier),
    }
    args.report.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
