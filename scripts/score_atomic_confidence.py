#!/usr/bin/env python3
"""Score generated atomic responses by conditional token likelihood."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import mlx.core as mx
from mlx_lm.utils import load


def load_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", required=True)
    parser.add_argument("--weights", type=Path, required=True)
    parser.add_argument("--prompts", type=Path, required=True)
    parser.add_argument("--predictions", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    prompts = {row["id"]: row["prompt"] for row in load_jsonl(args.prompts)}
    predictions = load_jsonl(args.predictions)
    model, tokenizer = load(args.model, tokenizer_config={"trust_remote_code": True})
    model.load_weights(str(args.weights), strict=True)
    rows = []
    for prediction in predictions:
        identifier, response = prediction["id"], prediction["response"]
        prompt_tokens = tokenizer.encode(prompts[identifier])
        response_tokens = tokenizer.encode(response)
        tokens = prompt_tokens + response_tokens
        logits = model(mx.array(tokens[:-1], dtype=mx.int32)[None, :])[0]
        start = len(prompt_tokens)
        positions = mx.arange(start - 1, start + len(response_tokens) - 1)
        selected = logits[positions]
        targets = mx.array(response_tokens, dtype=mx.int32)
        log_probs = selected[mx.arange(len(response_tokens)), targets] - mx.logsumexp(selected, axis=-1)
        rows.append({"id": identifier, "mean_log_probability": float(mx.mean(log_probs).item()), "minimum_log_probability": float(mx.min(log_probs).item()), "tokens": len(response_tokens)})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows), encoding="utf-8")
    print(json.dumps({"count": len(rows), "predictions_sha256": sha256(args.predictions), "scores_sha256": sha256(args.output), "peak_metal_gb": mx.get_peak_memory() / 1e9}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
