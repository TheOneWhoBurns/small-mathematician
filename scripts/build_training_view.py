#!/usr/bin/env python3
"""Build reproducible family-separated MLX training views from audited data."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path
from typing import Any

from transformers import AutoTokenizer


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_INPUT = ROOT / "assets" / "data" / "processed" / "audited" / "eligible-default.jsonl"
DEFAULT_MODEL = ROOT / "assets" / "models" / "qwen3-0.6b-base"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--model", type=Path, default=DEFAULT_MODEL)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--domain", action="append", help="Repeat to select domains; omit for all.")
    parser.add_argument(
        "--exclude-flag",
        action="append",
        help="Repeat to exclude audited quality flags (for example unresolved_cross_reference).",
    )
    parser.add_argument("--target-style", choices=("proof", "concept-proof"), default="proof")
    parser.add_argument("--max-tokens", type=int, default=1024)
    parser.add_argument("--max-rows", type=int)
    parser.add_argument("--order", choices=("hash", "short-first"), default="hash")
    parser.add_argument("--seed", type=int, default=17)
    parser.add_argument("--split-salt", default="small-mathematician-v1")
    parser.add_argument("--valid-percent", type=int, default=10)
    parser.add_argument("--test-percent", type=int, default=10)
    return parser.parse_args()


def digest_file(path: Path) -> str:
    hasher = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(8 * 1024 * 1024), b""):
            hasher.update(chunk)
    return hasher.hexdigest()


def stable_number(value: str, seed: int) -> int:
    raw = hashlib.sha256(f"{seed}:{value}".encode()).digest()
    return int.from_bytes(raw[:8], "big")


def domain_of(row: dict[str, Any]) -> str:
    return row["metadata"].get("domain", "fineproofs")


def format_example(row: dict[str, Any], style: str) -> dict[str, Any]:
    prompt = (
        "Problem: "
        + row["statement"].strip()
        + "\nProvide a correct natural-language proof or solution.\n"
    )
    if style == "concept-proof":
        labels = "; ".join(row["seed_concept_labels"]) or "infer the relevant ideas"
        completion = f"Relevant ideas: {labels}\nProof: {row['target_argument'].strip()}"
    else:
        completion = "Proof: " + row["target_argument"].strip()
    return {
        "prompt": prompt,
        "completion": completion,
        "metadata": {
            "id": row["id"],
            "family_id": row["family_id"],
            "domain": domain_of(row),
            "content_id": row["content_id"],
        },
    }


def split_for(family_id: str, salt: str, valid_percent: int, test_percent: int) -> str:
    digest = hashlib.sha256(f"{salt}|{family_id}".encode()).hexdigest()
    bucket = int(digest[:8], 16) % 100
    train_percent = 100 - valid_percent - test_percent
    if bucket < train_percent:
        return "train"
    if bucket < train_percent + valid_percent:
        return "valid"
    if bucket < 100:
        return "test"
    raise AssertionError("unreachable split bucket")


def main() -> None:
    args = parse_args()
    if args.valid_percent < 1 or args.test_percent < 1:
        raise ValueError("valid and test percentages must each be at least 1")
    if args.valid_percent + args.test_percent >= 50:
        raise ValueError("validation plus test percentage must be below 50")

    tokenizer = AutoTokenizer.from_pretrained(args.model, trust_remote_code=True)
    selected_domains = set(args.domain or [])
    excluded_flags = set(args.exclude_flag or [])
    examples: list[dict[str, Any]] = []
    rejected_too_long = Counter()
    with args.input.open(encoding="utf-8") as handle:
        for line in handle:
            row = json.loads(line)
            domain = domain_of(row)
            if selected_domains and domain not in selected_domains:
                continue
            if excluded_flags.intersection(row["quality"]["flags"]):
                continue
            example = format_example(row, args.target_style)
            token_count = len(tokenizer(example["prompt"] + example["completion"])["input_ids"])
            if token_count > args.max_tokens:
                rejected_too_long[domain] += 1
                continue
            example["metadata"]["tokens"] = token_count
            examples.append(example)

    if args.order == "short-first":
        examples.sort(key=lambda row: (row["metadata"]["tokens"], stable_number(row["metadata"]["content_id"], args.seed)))
    else:
        examples.sort(key=lambda row: stable_number(row["metadata"]["content_id"], args.seed))
    if args.max_rows is not None:
        examples = examples[: args.max_rows]

    splits: dict[str, list[dict[str, Any]]] = {"train": [], "valid": [], "test": []}
    for example in examples:
        split = split_for(
            example["metadata"]["family_id"],
            args.split_salt,
            args.valid_percent,
            args.test_percent,
        )
        splits[split].append(example)
    if not all(splits.values()):
        raise ValueError(f"one or more empty splits: { {name: len(rows) for name, rows in splits.items()} }")

    args.output.mkdir(parents=True, exist_ok=True)
    for split, rows in splits.items():
        with (args.output / f"{split}.jsonl").open("w", encoding="utf-8") as handle:
            for row in rows:
                handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")

    family_sets = {
        split: {row["metadata"]["family_id"] for row in rows}
        for split, rows in splits.items()
    }
    content_sets = {
        split: {row["metadata"]["content_id"] for row in rows}
        for split, rows in splits.items()
    }
    for left, right in (("train", "valid"), ("train", "test"), ("valid", "test")):
        if family_sets[left] & family_sets[right]:
            raise AssertionError(f"family leakage between {left} and {right}")
        if content_sets[left] & content_sets[right]:
            raise AssertionError(f"content leakage between {left} and {right}")
    manifest = {
        "schema_version": 1,
        "input": str(args.input.relative_to(ROOT)),
        "input_sha256": digest_file(args.input),
        "small_model_inputs": "natural-language statements only",
        "split_hash": f"sha256('{args.split_salt}|' + family_id)",
        "formal_data_read": False,
        "sealed_eval_data_read": False,
        "arguments": {
            key: str(value) if isinstance(value, Path) else value
            for key, value in vars(args).items()
        },
        "counts": {split: len(rows) for split, rows in splits.items()},
        "families": {split: len(families) for split, families in family_sets.items()},
        "by_domain": {
            split: dict(sorted(Counter(row["metadata"]["domain"] for row in rows).items()))
            for split, rows in splits.items()
        },
        "tokens": {
            split: sum(row["metadata"]["tokens"] for row in rows)
            for split, rows in splits.items()
        },
        "rejected_too_long": dict(sorted(rejected_too_long.items())),
    }
    (args.output / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
