#!/usr/bin/env python3
"""Evaluate an already sealed frozen method readout without refitting it."""

from __future__ import annotations

import argparse
import hashlib
import json
import time
from collections import Counter
from pathlib import Path

import mlx.core as mx
import numpy as np
from mlx_lm.models.base import create_attention_mask
from mlx_lm.utils import load


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def tokens(tokenizer, text: str) -> mx.array:
    content = "Respond only in English.\n" + text.rstrip() + "\nMethod:\n"
    values = tokenizer.apply_chat_template(
        [{"role": "user", "content": content}],
        add_generation_prompt=True,
        tokenize=True,
    )
    return mx.array(values, dtype=mx.int32)[None, :]


def feature(model, tokenizer, text: str, layer_index: int, pool: str) -> np.ndarray:
    input_ids = tokens(tokenizer, text)
    hidden = model.model.embed_tokens(input_ids)
    if layer_index > 0:
        mask = create_attention_mask(hidden, None)
        for index, layer in enumerate(model.model.layers, 1):
            hidden = layer(hidden, mask, None)
            if index == layer_index:
                break
    if layer_index == len(model.model.layers):
        hidden = model.model.norm(hidden)
    vector = hidden[0, -1] if pool == "last" else mx.mean(hidden[0], axis=0)
    vector = vector.astype(mx.float32)
    mx.eval(vector)
    return np.array(vector, copy=True)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", required=True)
    parser.add_argument("--weights", type=Path)
    parser.add_argument("--probe", type=Path, required=True)
    parser.add_argument("--expected-probe-sha256")
    parser.add_argument("--prompts", type=Path, required=True)
    parser.add_argument("--predictions", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()

    started = time.time()
    probe_hash = digest(args.probe)
    if args.expected_probe_sha256 and probe_hash != args.expected_probe_sha256:
        raise ValueError("sealed probe hash mismatch")
    archive = np.load(args.probe)
    mean = archive["mean"]
    scale = archive["scale"]
    weights = archive["weights"]
    classes = [str(value) for value in archive["classes"]]
    layer_index = int(archive["layer"])
    pool = str(archive["pool"])
    ridge = float(archive["ridge"])
    rows = read_jsonl(args.prompts)

    model, tokenizer = load(args.model, tokenizer_config={"trust_remote_code": True})
    if args.weights is not None:
        model.load_weights(list(mx.load(str(args.weights)).items()), strict=True)
    model.freeze()
    features = []
    for index, row in enumerate(rows, 1):
        features.append(feature(model, tokenizer, row["prompt"], layer_index, pool))
        if index % 50 == 0 or index == len(rows):
            print(f"features {index}/{len(rows)}", flush=True)
    matrix = np.stack(features)
    scores = ((matrix - mean) / scale) @ weights
    predicted = scores.argmax(axis=1)
    class_index = {label: index for index, label in enumerate(classes)}
    expected = np.array([class_index[row.get("family", row.get("route"))] for row in rows])

    args.predictions.parent.mkdir(parents=True, exist_ok=True)
    pair_correct: dict[str, list[bool]] = {}
    confusion: Counter[tuple[str, str]] = Counter()
    with args.predictions.open("w", encoding="utf-8") as handle:
        for row, gold, guess, row_scores in zip(rows, expected, predicted, scores):
            correct = bool(gold == guess)
            pair_id = row.get("pair_id")
            if pair_id:
                pair_correct.setdefault(pair_id, []).append(correct)
            confusion[(classes[int(gold)], classes[int(guess)])] += 1
            handle.write(
                json.dumps(
                    {
                        "id": row["id"],
                        "expected_route": classes[int(gold)],
                        "predicted_route": classes[int(guess)],
                        "correct": correct,
                        "pair_id": pair_id,
                        "scores": {label: float(score) for label, score in zip(classes, row_scores)},
                    },
                    sort_keys=True,
                )
                + "\n"
            )
    report = {
        "schema_version": 1,
        "evaluation_contract": "sealed frozen readout; no fitting or configuration selection",
        "model": args.model,
        "weights": str(args.weights) if args.weights else None,
        "weights_sha256": digest(args.weights) if args.weights else None,
        "probe": str(args.probe),
        "probe_sha256": probe_hash,
        "probe_parameters": int(weights.size),
        "probe_bytes": args.probe.stat().st_size,
        "configuration": {"layer": layer_index, "pool": pool, "ridge": ridge},
        "prompts": str(args.prompts),
        "prompts_sha256": digest(args.prompts),
        "count": len(rows),
        "accuracy": float(np.mean(expected == predicted)),
        "pairs": len(pair_correct),
        "pair_accuracy": (
            sum(len(values) == 2 and all(values) for values in pair_correct.values()) / len(pair_correct)
            if pair_correct else None
        ),
        "prediction_counts": dict(sorted(Counter(classes[int(value)] for value in predicted).items())),
        "confusion": [
            {"expected": gold, "predicted": guess, "count": count}
            for (gold, guess), count in sorted(confusion.items())
        ],
        "predictions_sha256": digest(args.predictions),
        "elapsed_seconds": time.time() - started,
        "prompts_per_second_including_load": len(rows) / (time.time() - started),
        "peak_metal_gb": mx.get_peak_memory() / 1e9,
    }
    args.report.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
