#!/usr/bin/env python3
"""Probe how accurately frozen hidden states encode decimal integers."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import random
import time
from collections import defaultdict
from pathlib import Path

import mlx.core as mx
import numpy as np
from mlx_lm.models.base import create_attention_mask
from mlx_lm.utils import load


LAYERS = (0, 7, 14, 21, 28)
RIDGES = (0.01, 0.1, 1.0, 10.0, 100.0)


def extract(model, tokenizer, maximum: int, batch_size: int) -> dict[int, np.ndarray]:
    tokenized = {number: tokenizer.encode(f"The integer is {number}") for number in range(1, maximum + 1)}
    by_length: dict[int, list[int]] = defaultdict(list)
    for number, tokens in tokenized.items():
        by_length[len(tokens)].append(number)
    chunks: dict[int, list[tuple[list[int], np.ndarray]]] = {layer: [] for layer in LAYERS}
    for numbers in by_length.values():
        for start in range(0, len(numbers), batch_size):
            batch_numbers = numbers[start : start + batch_size]
            tokens = mx.array([tokenized[number] for number in batch_numbers], dtype=mx.int32)
            hidden = model.model.embed_tokens(tokens)

            def record(layer: int, value: mx.array) -> None:
                vectors = value[:, -1, :].astype(mx.float32)
                mx.eval(vectors)
                chunks[layer].append((batch_numbers, np.array(vectors, copy=True)))

            record(0, hidden)
            mask = create_attention_mask(hidden, None)
            for layer_index, layer in enumerate(model.model.layers, 1):
                hidden = layer(hidden, mask, None)
                if layer_index in LAYERS and layer_index != 28:
                    record(layer_index, hidden)
            record(28, model.model.norm(hidden))
    result = {}
    for layer, parts in chunks.items():
        width = parts[0][1].shape[1]
        matrix = np.empty((maximum, width), dtype=np.float32)
        for numbers, vectors in parts:
            matrix[np.array(numbers) - 1] = vectors
        result[layer] = matrix
    return result


def normalized(train_x: np.ndarray, *others: np.ndarray) -> tuple[np.ndarray, ...]:
    mean = train_x.mean(axis=0)
    scale = train_x.std(axis=0)
    scale[scale < 1e-5] = 1.0
    return tuple((value - mean) / scale for value in (train_x, *others))


def ridge_predictions(train_x: np.ndarray, train_y: np.ndarray, *test_x: np.ndarray) -> dict[float, list[np.ndarray]]:
    kernel = train_x @ train_x.T
    eigenvalues, eigenvectors = np.linalg.eigh(kernel)
    projected = eigenvectors.T @ train_y
    outputs = {}
    for ridge in RIDGES:
        alpha = eigenvectors @ (projected / (eigenvalues[:, None] + ridge))
        weights = train_x.T @ alpha
        outputs[ridge] = [value @ weights for value in test_x]
    return outputs


def magnitude_probe(features: np.ndarray, train: np.ndarray, valid: np.ndarray, test: np.ndarray) -> dict:
    train_x, valid_x, test_x = normalized(features[train], features[valid], features[test])
    target = np.log10(np.arange(1, len(features) + 1, dtype=np.float64))[:, None]
    mean, scale = target[train].mean(), target[train].std()
    standardized = (target - mean) / scale
    trials = ridge_predictions(train_x, standardized[train], valid_x, test_x)
    selected = min(RIDGES, key=lambda ridge: float(np.mean((trials[ridge][0] - standardized[valid]) ** 2)))
    prediction = trials[selected][1] * scale + mean
    truth = target[test]
    residual = float(np.sum((prediction - truth) ** 2))
    total = float(np.sum((truth - truth.mean()) ** 2))
    return {
        "ridge": selected,
        "test_r2_log10": 1.0 - residual / total,
        "test_mae_log10": float(np.mean(np.abs(prediction - truth))),
    }


def digit_targets(maximum: int) -> np.ndarray:
    targets = np.full((maximum, 4), 10, dtype=np.int64)
    for number in range(1, maximum + 1):
        digits = str(number)[-4:].rjust(4, "_")
        targets[number - 1] = [10 if value == "_" else int(value) for value in digits]
    return targets


def digit_probe(features: np.ndarray, train: np.ndarray, valid: np.ndarray, test: np.ndarray) -> dict:
    train_x, valid_x, test_x = normalized(features[train], features[valid], features[test])
    targets = digit_targets(len(features))
    one_hot = np.eye(11, dtype=np.float32)[targets].reshape(len(features), 44)
    trials = ridge_predictions(train_x, one_hot[train], valid_x, test_x)

    def decode(scores: np.ndarray) -> np.ndarray:
        return scores.reshape(len(scores), 4, 11).argmax(axis=2)

    selected = max(RIDGES, key=lambda ridge: float(np.mean(decode(trials[ridge][0]) == targets[valid])))
    prediction = decode(trials[selected][1])
    return {
        "ridge": selected,
        "test_digit_accuracy": float(np.mean(prediction == targets[test])),
        "test_exact_number_accuracy": float(np.mean(np.all(prediction == targets[test], axis=1))),
        "per_place_accuracy": [float(np.mean(prediction[:, index] == targets[test, index])) for index in range(4)],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", required=True)
    parser.add_argument("--weights", type=Path)
    parser.add_argument("--maximum", type=int, default=2500)
    parser.add_argument("--batch-size", type=int, default=64)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    started = time.time()
    model, tokenizer = load(args.model, tokenizer_config={"trust_remote_code": True})
    if args.weights:
        model.load_weights(str(args.weights), strict=True)
    model.freeze()
    feature_sets = extract(model, tokenizer, args.maximum, args.batch_size)
    numbers = list(range(args.maximum))
    random.Random(20260828).shuffle(numbers)
    interpolation_train = np.array(numbers[:1000])
    interpolation_valid = np.array(numbers[1000:1500])
    interpolation_test = np.array(numbers[1500:])
    extrapolation_train = np.arange(0, 700)
    extrapolation_valid = np.arange(700, 1000)
    extrapolation_test = np.arange(1000, args.maximum)
    layers = {}
    for layer, features in feature_sets.items():
        layers[str(layer)] = {
            "interpolation_magnitude": magnitude_probe(features, interpolation_train, interpolation_valid, interpolation_test),
            "extrapolation_magnitude": magnitude_probe(features, extrapolation_train, extrapolation_valid, extrapolation_test),
            "interpolation_digits": digit_probe(features, interpolation_train, interpolation_valid, interpolation_test),
        }
    report = {
        "model": args.model,
        "weights": str(args.weights) if args.weights else None,
        "weights_sha256": hashlib.sha256(args.weights.read_bytes()).hexdigest() if args.weights else None,
        "maximum": args.maximum,
        "layers": layers,
        "elapsed_seconds": time.time() - started,
        "peak_metal_gb": mx.get_peak_memory() / 1e9,
        "interpretation_boundary": "Linear ridge probes are lower bounds on decodability and do not establish causal use.",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
