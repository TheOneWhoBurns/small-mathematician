#!/usr/bin/env python3
"""Select the first externally verified Euclidean trace from multiple samples."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

from evaluate_diophantine_traces import verify


def load(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--candidate", type=Path, action="append", required=True)
    parser.add_argument("--verifier", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()

    expected = load(args.verifier)
    expected_by_id = {row["id"]: row for row in expected}
    candidate_maps = []
    for path in args.candidate:
        rows = load(path)
        mapping = {row["id"]: row["response"] for row in rows}
        if mapping.keys() != expected_by_id.keys():
            raise ValueError(f"candidate IDs do not match verifier: {path}")
        candidate_maps.append(mapping)

    selected = []
    selected_arms = Counter()
    coverage_by_prefix = []
    for prefix_count in range(1, len(candidate_maps) + 1):
        coverage_by_prefix.append(
            sum(
                any(verify(candidate[example_id], row)["trace_valid"] for candidate in candidate_maps[:prefix_count])
                for example_id, row in expected_by_id.items()
            )
        )
    per_surface = {}
    for surface in sorted({row.get("surface", "unspecified") for row in expected}):
        surface_rows = [row for row in expected if row.get("surface", "unspecified") == surface]
        per_surface[surface] = {
            "count": len(surface_rows),
            "coverage_by_prefix": [
                sum(
                    any(verify(candidate[row["id"]], row)["trace_valid"] for candidate in candidate_maps[:prefix_count])
                    for row in surface_rows
                )
                for prefix_count in range(1, len(candidate_maps) + 1)
            ],
        }

    for row in expected:
        example_id = row["id"]
        arm = 0
        for index, candidate in enumerate(candidate_maps):
            if verify(candidate[example_id], row)["trace_valid"]:
                arm = index
                break
        selected_arms[arm] += 1
        selected.append({"id": example_id, "response": candidate_maps[arm][example_id]})

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        "".join(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n" for row in selected),
        encoding="utf-8",
    )
    report = {
        "count": len(expected),
        "candidates": len(candidate_maps),
        "selection_metric": "trace_valid only",
        "coverage_by_prefix": coverage_by_prefix,
        "per_surface": per_surface,
        "selected_arm_counts": dict(sorted(selected_arms.items())),
        "candidate_sha256": [sha256(path) for path in args.candidate],
        "verifier_sha256": sha256(args.verifier),
        "output_sha256": sha256(args.output),
    }
    args.report.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
