#!/usr/bin/env python3
"""Decompose Diophantine atomic-claim accuracy into extraction and arithmetic parts."""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from pathlib import Path


PATTERN = re.compile(
    r"The greatest common divisor is (-?\d+),? and it (does|does not) divide (-?\d+)\.?"
)


def load_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def summarize(rows: list[dict]) -> dict:
    count = len(rows)
    totals = Counter()
    for row in rows:
        for key in ("parsed", "target_extracted", "gcd_correct", "relation_correct", "internally_consistent", "semantic"):
            totals[key] += int(row[key])
    result = {"count": count}
    for key, value in totals.items():
        result[key] = value
        result[key + "_rate"] = value / count
    gcd_correct = [row for row in rows if row["gcd_correct"]]
    result["relation_correct_given_gcd_correct"] = (
        sum(int(row["relation_correct"]) for row in gcd_correct) / len(gcd_correct)
        if gcd_correct
        else None
    )
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--predictions", type=Path, required=True)
    parser.add_argument("--verifier", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    predictions = {row["id"]: row["response"].strip() for row in load_jsonl(args.predictions)}
    verifier = load_jsonl(args.verifier)
    if predictions.keys() != {row["id"] for row in verifier}:
        raise ValueError("prediction IDs do not match verifier IDs")

    details = []
    for row in verifier:
        params = row["parameters"]
        match = PATTERN.fullmatch(predictions[row["id"]])
        proposed_gcd = int(match.group(1)) if match else None
        proposed_relation = match.group(2) if match else None
        proposed_target = int(match.group(3)) if match else None
        expected_relation = "does" if params["solvable"] else "does not"
        internally_consistent = bool(
            match
            and proposed_gcd != 0
            and ((proposed_target % proposed_gcd == 0) == (proposed_relation == "does"))
        )
        details.append(
            {
                "id": row["id"],
                "surface": row.get("surface", "unspecified"),
                "parsed": bool(match),
                "target_extracted": proposed_target == params["c"],
                "gcd_correct": proposed_gcd == params["gcd"],
                "relation_correct": proposed_relation == expected_relation,
                "internally_consistent": internally_consistent,
                "semantic": bool(match and proposed_target == params["c"] and proposed_gcd == params["gcd"] and proposed_relation == expected_relation),
            }
        )

    surfaces = sorted({row["surface"] for row in details})
    report = {
        "overall": summarize(details),
        "per_surface": {surface: summarize([row for row in details if row["surface"] == surface]) for surface in surfaces},
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
