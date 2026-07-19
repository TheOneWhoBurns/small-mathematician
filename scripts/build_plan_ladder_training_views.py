#!/usr/bin/env python3
"""Build paired raw and completion-masked training views for the plan ladder."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from transformers import AutoTokenizer


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--data", type=Path, required=True)
    parser.add_argument("--model", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    args = parser.parse_args()

    tokenizer = AutoTokenizer.from_pretrained(args.model, trust_remote_code=True)
    conditions = ("free", "ordered")
    counts: dict[str, int] = {}
    token_totals = {condition: {} for condition in conditions}
    pair_deltas: dict[str, list[int]] = {}
    source_hashes: dict[str, dict[str, str]] = {}

    for split in ("train", "valid"):
        prompt_path = args.data / f"{split}.prompts.jsonl"
        target_path = args.data / f"{split}.targets.jsonl"
        prompts = read_jsonl(prompt_path)
        targets = {row["id"]: row for row in read_jsonl(target_path)}
        if len(targets) != len(prompts) or {row["id"] for row in prompts} != set(targets):
            raise ValueError(f"prompt/target ID mismatch in {split}")
        counts[split] = len(prompts)
        source_hashes[split] = {
            "prompts": sha256(prompt_path),
            "targets": sha256(target_path),
        }
        pair_deltas[split] = []
        rendered_by_condition: dict[str, list[dict]] = {condition: [] for condition in conditions}
        completions_by_condition: dict[str, list[dict]] = {
            condition: [] for condition in conditions
        }
        per_condition_tokens: dict[str, dict[str, int]] = {condition: {} for condition in conditions}
        for prompt_row in prompts:
            example_id = prompt_row["id"]
            target_row = targets[example_id]
            for condition in conditions:
                prompt = (
                    "Respond only in English.\n"
                    + prompt_row["prompt"].rstrip()
                    + "\nPlan:\n"
                )
                completion = target_row[f"target_{condition}"].strip()
                text = prompt + completion
                tokens = len(tokenizer(text)["input_ids"])
                per_condition_tokens[condition][example_id] = tokens
                rendered_by_condition[condition].append(
                    {
                        "text": text,
                        "metadata": {
                            "id": example_id,
                            "family": prompt_row["family"],
                            "condition": condition,
                            "tokens": tokens,
                        },
                    }
                )
                completions_by_condition[condition].append(
                    {
                        "prompt": prompt,
                        "completion": completion,
                        "metadata": {
                            "id": example_id,
                            "family": prompt_row["family"],
                            "condition": condition,
                        },
                    }
                )
        for example_id in targets:
            pair_deltas[split].append(
                abs(
                    per_condition_tokens["free"][example_id]
                    - per_condition_tokens["ordered"][example_id]
                )
            )
        for condition in conditions:
            output_dir = args.output_root / f"verified-plan-ladder-{condition}-raw"
            output_dir.mkdir(parents=True, exist_ok=True)
            output_path = output_dir / f"{split}.jsonl"
            with output_path.open("w", encoding="utf-8") as handle:
                for row in rendered_by_condition[condition]:
                    handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
            completion_dir = args.output_root / f"verified-plan-ladder-{condition}-completion"
            completion_dir.mkdir(parents=True, exist_ok=True)
            completion_path = completion_dir / f"{split}.jsonl"
            with completion_path.open("w", encoding="utf-8") as handle:
                for row in completions_by_condition[condition]:
                    handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
            token_totals[condition][split] = sum(per_condition_tokens[condition].values())

    aggregate_tokens = {condition: sum(values.values()) for condition, values in token_totals.items()}
    aggregate_ratio = abs(aggregate_tokens["free"] - aggregate_tokens["ordered"]) / max(
        aggregate_tokens.values()
    )
    if aggregate_ratio > 0.05:
        raise ValueError(f"paired tokenizer-token totals differ by {aggregate_ratio:.3%}")

    common_manifest = {
        "schema_version": 1,
        "source_data": str(args.data),
        "source_sha256": source_hashes,
        "model_tokenizer": str(args.model),
        "counts": counts,
        "token_totals": token_totals,
        "aggregate_tokens": aggregate_tokens,
        "aggregate_token_ratio": aggregate_ratio,
        "max_pair_token_delta": max(delta for values in pair_deltas.values() for delta in values),
        "chat_template_used": False,
        "small_model_input": "ordinary-English mathematical statement only",
        "small_model_output": "ordinary-English mathematical plan only",
        "formal_data_read": False,
    }
    for condition in conditions:
        for objective in ("raw", "completion"):
            output_dir = args.output_root / f"verified-plan-ladder-{condition}-{objective}"
            manifest = {
                **common_manifest,
                "condition": condition,
                "objective": objective,
                "mask_prompt": objective == "completion",
                "chat_template_used": objective == "completion",
            }
            (output_dir / "manifest.json").write_text(
                json.dumps(manifest, indent=2, sort_keys=True) + "\n"
            )
    print(json.dumps(common_manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
