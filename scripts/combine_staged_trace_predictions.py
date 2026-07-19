#!/usr/bin/env python3
"""Combine staged natural-language trace prefixes and continuations."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def load(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--staged-prompts", type=Path, required=True)
    parser.add_argument("--continuations", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    staged = {row["id"]: row for row in load(args.staged_prompts)}
    continuations = {row["id"]: row for row in load(args.continuations)}
    if staged.keys() != continuations.keys():
        raise ValueError("staged-prompt and continuation IDs do not match")
    rows = []
    for problem_id, row in staged.items():
        prefix = row["prefix"].strip()
        continuation = continuations[problem_id]["response"].strip()
        response = (prefix + " " + continuation).strip()
        rows.append({"id": problem_id, "response": response})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows), encoding="utf-8")
    manifest = {
        "count": len(rows),
        "staged_prompts_sha256": digest(args.staged_prompts),
        "continuations_sha256": digest(args.continuations),
        "output_sha256": digest(args.output),
    }
    args.output.with_suffix(args.output.suffix + ".manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
