#!/usr/bin/env python3
"""Create story-shell-disjoint contrast routing train/validation/test views."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


SHELL_SPLITS = {
    "archive desk": "train",
    "materials laboratory": "train",
    "transit office": "train",
    "community garden": "valid",
    "repair workshop": "test",
}


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--prompts", type=Path, required=True)
    parser.add_argument("--method-manifest", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    methods = json.loads(args.method_manifest.read_text())["methods"]
    buckets: dict[str, list[dict]] = {"train": [], "valid": [], "test": []}
    prompt_buckets: dict[str, list[dict]] = {"train": [], "valid": [], "test": []}
    for row in read_jsonl(args.prompts):
        split = SHELL_SPLITS[row["story_shell"]]
        prompt_buckets[split].append(row)
        buckets[split].append(
            {
                "prompt": "Respond only in English.\n" + row["prompt"] + "\nMethod:\n",
                "completion": methods[row["route"]],
                "metadata": {
                    "id": row["id"],
                    "family": row["route"],
                    "pair_id": row["pair_id"],
                    "story_shell": row["story_shell"],
                },
            }
        )
    args.output.mkdir(parents=True, exist_ok=True)
    for split in ("train", "valid", "test"):
        with (args.output / f"{split}.jsonl").open("w", encoding="utf-8") as handle:
            for row in buckets[split]:
                handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
        with (args.output / f"{split}.prompts.jsonl").open("w", encoding="utf-8") as handle:
            for row in prompt_buckets[split]:
                handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
    manifest = {
        "schema_version": 1,
        "source": str(args.prompts),
        "source_sha256": sha256(args.prompts),
        "shell_splits": SHELL_SPLITS,
        "counts": {split: len(rows) for split, rows in buckets.items()},
        "pairs": {split: len(rows) // 2 for split, rows in buckets.items()},
        "gold_method_from": "public route label in contrast construction",
        "claim": "story-shell-disjoint route acquisition only",
    }
    (args.output / "manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
