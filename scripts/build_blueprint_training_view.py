#!/usr/bin/env python3
"""Build a raw natural-language proof-blueprint training view."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def split_for(family_id: str) -> str:
    bucket = int(
        hashlib.sha256(f"blueprint-pilot-split-v1|{family_id}".encode()).hexdigest()[:8],
        16,
    ) % 10
    if bucket < 8:
        return "train"
    if bucket == 8:
        return "valid"
    return "test"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--teacher-dir", type=Path, action="append", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    input_paths = sorted(
        path for directory in args.teacher_dir for path in directory.glob("teacher-input-*.jsonl")
    )
    output_paths = sorted(
        path for directory in args.teacher_dir for path in directory.glob("teacher-output-*.jsonl")
    )
    if not input_paths or len(input_paths) != len(output_paths):
        raise ValueError("teacher input/output shard counts must match and be nonzero")

    input_rows = [row for path in input_paths for row in read_jsonl(path)]
    output_rows = [row for path in output_paths for row in read_jsonl(path)]
    inputs = {row["id"]: row for row in input_rows}
    outputs = {row["id"]: row for row in output_rows}
    if len(inputs) != len(input_rows) or len(outputs) != len(output_rows):
        raise ValueError("duplicate teacher IDs across shards or directories")
    if set(inputs) != set(outputs):
        missing = sorted(set(inputs) - set(outputs))
        extra = sorted(set(outputs) - set(inputs))
        raise ValueError(f"teacher ID mismatch: missing={missing[:3]} extra={extra[:3]}")

    splits: dict[str, list[dict]] = {"train": [], "valid": [], "test": []}
    word_counts: list[int] = []
    for example_id in sorted(inputs):
        source = inputs[example_id]
        teacher = outputs[example_id]
        if source["family_id"] != teacher["family_id"]:
            raise ValueError(f"family mismatch for {example_id}")
        blueprint = " ".join(teacher["blueprint"].split())
        words = len(blueprint.split())
        if not 35 <= words <= 170:
            raise ValueError(f"blueprint length {words} outside 35..170 for {example_id}")
        word_counts.append(words)

        problem = source["problem"].strip()
        instruction = "Provide a correct natural-language proof or solution."
        if problem.endswith(instruction):
            problem = problem[: -len(instruction)].rstrip()
        text = (
            problem
            + "\nProvide a concise natural-language proof blueprint: state the central idea "
            + "and the necessary logical steps.\nSolution:\nBlueprint: "
            + blueprint
        )
        splits[split_for(source["family_id"])].append(
            {
                "text": text,
                "metadata": {
                    "id": example_id,
                    "family_id": source["family_id"],
                    "teacher": "external-frontier-language-model",
                    "target": "ordinary-language-proof-blueprint",
                },
            }
        )

    if not all(splits.values()):
        raise ValueError(f"empty split: { {key: len(value) for key, value in splits.items()} }")
    args.output.mkdir(parents=True, exist_ok=True)
    for split, rows in splits.items():
        path = args.output / f"{split}.jsonl"
        with path.open("w", encoding="utf-8") as handle:
            for row in rows:
                handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")

    manifest = {
        "schema_version": 1,
        "teacher_dir": [str(directory) for directory in args.teacher_dir],
        "teacher_input_sha256": {str(path): sha256(path) for path in input_paths},
        "teacher_output_sha256": {str(path): sha256(path) for path in output_paths},
        "counts": {split: len(rows) for split, rows in splits.items()},
        "split": "sha256('blueprint-pilot-split-v1|' + family_id), 80/10/10",
        "training_split_only_source": True,
        "small_model_input": "natural-language mathematical statement only",
        "target": "ordinary-language proof blueprint",
        "blueprint_words": {
            "min": min(word_counts),
            "max": max(word_counts),
            "mean": sum(word_counts) / len(word_counts),
        },
    }
    (args.output / "manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
