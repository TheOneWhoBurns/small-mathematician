#!/usr/bin/env python3
"""Verify natural-language Euclidean traces and their final Diophantine claim."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from collections import Counter
from pathlib import Path


STEP = re.compile(r"Euclidean step: (-?\d+) = (-?\d+) times (-?\d+) plus (-?\d+)\.")
FINAL = re.compile(r"Therefore the greatest common divisor is (-?\d+),? and it (does|does not) divide (-?\d+)\.")


def load_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify(response: str, row: dict) -> dict:
    response = " ".join(response.strip().split())
    matches = list(STEP.finditer(response))
    final = FINAL.search(response)
    parsed = bool(matches and final and final.end() == len(response) and matches[0].start() == 0)
    trace_valid = parsed
    if parsed:
        a, b = row["parameters"]["a"], row["parameters"]["b"]
        expected_dividend, expected_divisor = max(a, b), min(a, b)
        cursor = 0
        for match in matches:
            dividend, quotient, divisor, remainder = map(int, match.groups())
            if response[cursor:match.start()].strip():
                trace_valid = False
            if (dividend, divisor) != (expected_dividend, expected_divisor):
                trace_valid = False
            if divisor <= 0 or quotient < 0 or remainder < 0 or remainder >= divisor:
                trace_valid = False
            if dividend != quotient * divisor + remainder:
                trace_valid = False
            expected_dividend, expected_divisor = divisor, remainder
            cursor = match.end()
        if response[cursor:final.start()].strip() or expected_divisor != 0:
            trace_valid = False
    params = row["parameters"]
    expected_relation = "does" if params["solvable"] else "does not"
    final_valid = bool(
        final
        and int(final.group(1)) == params["gcd"]
        and final.group(2) == expected_relation
        and int(final.group(3)) == params["c"]
    )
    return {"parsed": parsed, "trace_valid": trace_valid, "final_valid": final_valid, "semantic": trace_valid and final_valid}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--predictions", type=Path, required=True)
    parser.add_argument("--verifier", type=Path, required=True)
    parser.add_argument("--details", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    predictions = {row["id"]: row["response"] for row in load_jsonl(args.predictions)}
    expected = load_jsonl(args.verifier)
    if predictions.keys() != {row["id"] for row in expected}:
        raise ValueError("prediction IDs do not match verifier IDs")
    details = []
    for row in expected:
        result = verify(predictions[row["id"]], row)
        details.append({"id": row["id"], "family": row["family"], "surface": row.get("surface", "unspecified"), "response": predictions[row["id"]], **result})
    args.details.parent.mkdir(parents=True, exist_ok=True)
    args.details.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in details), encoding="utf-8")
    totals = Counter()
    for row in details:
        for key in ("parsed", "trace_valid", "final_valid", "semantic"):
            totals[key] += int(row[key])
    count = len(details)
    surfaces = sorted({row["surface"] for row in details})
    per_surface = {}
    for surface in surfaces:
        surface_rows = [row for row in details if row["surface"] == surface]
        surface_totals = Counter()
        for row in surface_rows:
            for key in ("parsed", "trace_valid", "final_valid", "semantic"):
                surface_totals[key] += int(row[key])
        surface_count = len(surface_rows)
        per_surface[surface] = {
            "count": surface_count,
            **{key: surface_totals[key] for key in surface_totals},
            **{key + "_rate": surface_totals[key] / surface_count for key in surface_totals},
        }
    report = {"count": count, **{key: totals[key] for key in totals}, **{key + "_rate": totals[key] / count for key in totals}, "per_surface": per_surface, "predictions_sha256": sha256(args.predictions), "verifier_sha256": sha256(args.verifier)}
    args.report.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
