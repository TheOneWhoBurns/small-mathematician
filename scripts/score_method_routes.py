#!/usr/bin/env python3
"""Choose among natural-language mathematical methods by conditional likelihood."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import time
from collections import Counter
from pathlib import Path

import mlx.core as mx
from mlx_lm.utils import load


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def find_subsequence(sequence: list[int], subsequence: list[int]) -> int:
    for start in range(len(sequence) - len(subsequence) + 1):
        if sequence[start:start + len(subsequence)] == subsequence:
            return start
    raise ValueError("method token sequence not found in chat rendering")


def method_mean_log_probability(model, tokenizer, user_prompt: str, method: str) -> float:
    messages = [
        {"role": "user", "content": user_prompt},
        {"role": "assistant", "content": method},
    ]
    tokens = tokenizer.apply_chat_template(messages, return_dict=False)
    method_tokens = tokenizer.encode(method, add_special_tokens=False)
    start = find_subsequence(tokens, method_tokens)
    inputs = mx.array(tokens[:-1], dtype=mx.int32)[None, :]
    logits = model(inputs)[0]
    positions = mx.arange(start - 1, start + len(method_tokens) - 1)
    selected = logits[positions]
    targets = mx.array(method_tokens, dtype=mx.int32)
    correct = selected[mx.arange(len(method_tokens)), targets]
    log_probabilities = correct - mx.logsumexp(selected, axis=-1)
    value = float(mx.mean(log_probabilities).item())
    return value


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", required=True)
    parser.add_argument("--weights", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--prompts", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--prompt-prefix", default="Respond only in English.\n")
    parser.add_argument("--prompt-suffix", default="\nMethod:\n")
    parser.add_argument("--deadline")
    args = parser.parse_args()

    manifest = json.loads(args.manifest.read_text())
    methods: dict[str, str] = manifest["methods"]
    prompts = read_jsonl(args.prompts)
    model, tokenizer = load(args.model, tokenizer_config={"trust_remote_code": True})
    model.load_weights(list(mx.load(str(args.weights)).items()), strict=True)
    deadline = __import__("datetime").datetime.fromisoformat(args.deadline) if args.deadline else None

    args.output.parent.mkdir(parents=True, exist_ok=True)
    details: list[dict] = []
    started = time.time()
    with args.output.open("w", encoding="utf-8") as handle:
        for index, row in enumerate(prompts, 1):
            if deadline and __import__("datetime").datetime.now(deadline.tzinfo) >= deadline:
                break
            user_prompt = args.prompt_prefix + row["prompt"].rstrip() + args.prompt_suffix
            scores = {
                route: method_mean_log_probability(model, tokenizer, user_prompt, method)
                for route, method in methods.items()
            }
            predicted = max(scores, key=scores.get)
            ranked = sorted(scores, key=scores.get, reverse=True)
            detail = {
                "id": row["id"],
                "expected_route": row.get("route", row.get("family")),
                "predicted_route": predicted,
                "correct": predicted == row.get("route", row.get("family")),
                "margin": scores[ranked[0]] - scores[ranked[1]],
                "mean_log_probability": scores,
                "pair_id": row.get("pair_id"),
            }
            details.append(detail)
            handle.write(json.dumps(detail, sort_keys=True) + "\n")
            handle.flush()
            print(f"{index}/{len(prompts)} {row['id']} {predicted}", flush=True)

    evaluated = [row for row in details if isinstance(row["expected_route"], str)]
    confusion: Counter[tuple[str, str]] = Counter(
        (row["expected_route"], row["predicted_route"]) for row in evaluated
    )
    pair_groups: dict[str, list[bool]] = {}
    for row in evaluated:
        if row["pair_id"]:
            pair_groups.setdefault(row["pair_id"], []).append(row["correct"])
    report = {
        "schema_version": 1,
        "selection": "highest mean teacher-forced log probability of five natural-language method descriptions",
        "model": args.model,
        "weights": str(args.weights),
        "weights_sha256": sha256(args.weights),
        "prompts": str(args.prompts),
        "prompts_sha256": sha256(args.prompts),
        "count": len(evaluated),
        "accuracy": sum(row["correct"] for row in evaluated) / len(evaluated) if evaluated else math.nan,
        "mean_margin": sum(row["margin"] for row in evaluated) / len(evaluated) if evaluated else math.nan,
        "pairs": len(pair_groups),
        "pair_accuracy": (
            sum(len(values) == 2 and all(values) for values in pair_groups.values()) / len(pair_groups)
            if pair_groups else None
        ),
        "confusion": [
            {"expected": expected, "predicted": predicted, "count": count}
            for (expected, predicted), count in sorted(confusion.items())
        ],
        "elapsed_seconds": time.time() - started,
        "deadline": args.deadline,
    }
    report_path = args.output.with_suffix(args.output.suffix + ".report.json")
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
