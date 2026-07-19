#!/usr/bin/env python3
"""Merge sealed trace-test parts while assigning public evaluation bands."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def load(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def write(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows), encoding="utf-8")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--part", nargs=3, action="append", metavar=("LABEL", "PROMPTS", "VERIFIER"), required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    prompts: list[dict] = []
    verifier: list[dict] = []
    ids: set[str] = set()
    parameters: set[tuple[int, int, int]] = set()
    counts = {}
    for label, prompts_path, verifier_path in args.part:
        public_rows = load(Path(prompts_path))
        private_rows = load(Path(verifier_path))
        if [row["id"] for row in public_rows] != [row["id"] for row in private_rows]:
            raise ValueError(f"ID mismatch in {label}")
        counts[label] = len(public_rows)
        for public, private in zip(public_rows, private_rows):
            if public["id"] in ids:
                raise ValueError(f"duplicate ID {public['id']}")
            ids.add(public["id"])
            params = private["parameters"]
            key = (params["a"], params["b"], params["c"])
            if key in parameters:
                raise ValueError(f"duplicate parameters {key}")
            parameters.add(key)
            prompts.append({**public, "surface": label})
            verifier.append({**private, "surface": label})
    write(args.output_dir / "test.prompts.jsonl", prompts)
    write(args.output_dir / "test.verifier.jsonl", verifier)
    manifest = {
        "counts": counts,
        "total": len(prompts),
        "parameter_overlap": 0,
        "test_prompt_sha256": sha256(args.output_dir / "test.prompts.jsonl"),
        "test_verifier_sha256": sha256(args.output_dir / "test.verifier.jsonl"),
    }
    (args.output_dir / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
