#!/usr/bin/env python3
"""Apply a faithful verifier to sealed atomic candidates and report coverage."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import defaultdict
from pathlib import Path

from evaluate_atomic_claims import normalize, semantically_valid


def load_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--candidates", type=Path, required=True)
    parser.add_argument("--verifier", type=Path, required=True)
    parser.add_argument("--accepted", type=Path, required=True)
    args = parser.parse_args()

    expected = {row["id"]: row for row in load_jsonl(args.verifier)}
    grouped: dict[str, list[dict]] = defaultdict(list)
    for candidate in load_jsonl(args.candidates):
        grouped[candidate["id"]].append(candidate)
    if set(grouped) != set(expected):
        raise ValueError("candidate and verifier IDs differ")
    accepted = []
    candidate_valid = 0
    unique_counts = []
    for identifier, row in expected.items():
        candidates = grouped[identifier]
        unique_counts.append(len({normalize(candidate["response"]) for candidate in candidates}))
        valid = [candidate for candidate in candidates if semantically_valid(normalize(candidate["response"]), row)]
        candidate_valid += len(valid)
        if valid:
            accepted.append({**valid[0], "semantic": True})
    args.accepted.parent.mkdir(parents=True, exist_ok=True)
    args.accepted.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in accepted), encoding="utf-8")
    report = {
        "prompts": len(expected),
        "candidates": sum(len(rows) for rows in grouped.values()),
        "candidate_valid": candidate_valid,
        "accepted": len(accepted),
        "coverage": len(accepted) / len(expected),
        "accepted_precision": 1.0 if accepted else None,
        "mean_unique_candidates": sum(unique_counts) / len(unique_counts),
        "candidates_sha256": sha256(args.candidates),
        "verifier_sha256": sha256(args.verifier),
        "accepted_sha256": sha256(args.accepted),
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
