#!/usr/bin/env python3
"""Build natural-language single-step Euclidean-division curriculum and sealed test."""

from __future__ import annotations

import argparse
import hashlib
import json
import random
from pathlib import Path


SURFACES = {
    "small": (50, 216),
    "medium": (501, 1000),
    "large": (1001, 2500),
}

TEMPLATES = (
    "Perform one Euclidean-division step with dividend {dividend} and divisor {divisor}.",
    "Divide {dividend} by {divisor}, keeping the exact integer quotient and remainder.",
    "What is the quotient-with-remainder decomposition of {dividend} by {divisor}?",
    "Express {dividend} as an integer multiple of {divisor} plus the least nonnegative remainder.",
)


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def make_rows(rng: random.Random, split: str, per_surface: int, used: set[tuple[int, int]]) -> list[dict]:
    rows = []
    for surface, (low, high) in SURFACES.items():
        made = 0
        while made < per_surface:
            dividend = rng.randint(low, high)
            # Draw logarithmically enough to expose both large and small quotients.
            if made % 2:
                divisor = rng.randint(2, min(dividend, 40))
            else:
                divisor = rng.randint(max(2, dividend // 12), dividend)
            key = (dividend, divisor)
            if key in used:
                continue
            used.add(key)
            quotient, remainder = divmod(dividend, divisor)
            template = TEMPLATES[made % len(TEMPLATES)]
            prompt = (
                "Respond only in English.\n"
                f"Problem: {template.format(dividend=dividend, divisor=divisor)}\n"
                "Relevant concept: Euclidean division.\n"
                "Task: Give exactly one step in the form 'Euclidean step: A = Q times B plus R.'\n"
                "Argument: "
            )
            completion = f"Euclidean step: {dividend} = {quotient} times {divisor} plus {remainder}."
            identifier = f"esv14-{surface}-{split}-{made:04d}"
            rows.append({
                "id": identifier,
                "family": "euclidean_single_step",
                "split": split,
                "surface": surface,
                "prompt": prompt,
                "completion": completion,
                "expected": completion,
                "parameters": {
                    "dividend": dividend,
                    "divisor": divisor,
                    "quotient": quotient,
                    "remainder": remainder,
                },
            })
            made += 1
    return rows


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--train-per-surface", type=int, default=1000)
    parser.add_argument("--valid-per-surface", type=int, default=160)
    parser.add_argument("--test-per-surface", type=int, default=200)
    parser.add_argument("--seed", type=int, default=20260719)
    args = parser.parse_args()

    rng = random.Random(args.seed)
    used: set[tuple[int, int]] = set()
    rows_by_split = {
        "train": make_rows(rng, "train", args.train_per_surface, used),
        "valid": make_rows(rng, "valid", args.valid_per_surface, used),
        "test": make_rows(rng, "test", args.test_per_surface, used),
    }
    for split, rows in rows_by_split.items():
        write_jsonl(
            args.output_dir / f"{split}.prompts.jsonl",
            [{"id": row["id"], "family": row["family"], "surface": row["surface"], "prompt": row["prompt"]} for row in rows],
        )
        write_jsonl(args.output_dir / f"{split}.verifier.jsonl", rows)
        if split != "test":
            write_jsonl(
                args.output_dir / "training" / f"{split}.jsonl",
                [{"prompt": row["prompt"], "completion": row["completion"], "metadata": {"id": row["id"], "family": row["family"], "surface": row["surface"]}} for row in rows],
            )
    manifest = {
        "schema_version": 1,
        "seed": args.seed,
        "surfaces": SURFACES,
        "counts": {split: len(rows) for split, rows in rows_by_split.items()},
        "unique_parameter_pairs": len(used),
        "parameter_overlap": 0,
        "test_prompt_sha256": sha256(args.output_dir / "test.prompts.jsonl"),
        "test_verifier_sha256": sha256(args.output_dir / "test.verifier.jsonl"),
    }
    (args.output_dir / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
