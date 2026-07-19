#!/usr/bin/env python3
"""Fit a tiny frozen linear readout for mathematical method concepts.

Probe selection uses the training and paraphrase splits only.  The matched
contrast set is not opened until the selected configuration has been sealed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import time
from collections import Counter
from pathlib import Path

import mlx.core as mx
import numpy as np
from mlx_lm.utils import load


LAYERS = (0, 7, 14, 21, 28)
POOLS = ("last", "mean")
RIDGES = (0.001, 0.01, 0.1, 1.0, 10.0, 100.0)


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def prompt_tokens(tokenizer, text: str, raw_prompts: bool = False) -> list[int]:
    if raw_prompts:
        return tokenizer.encode(text)
    content = "Respond only in English.\n" + text.rstrip() + "\nMethod:\n"
    return tokenizer.apply_chat_template(
        [{"role": "user", "content": content}],
        add_generation_prompt=True,
        tokenize=True,
    )


def extract(model, tokenizer, rows: list[dict], raw_prompts: bool = False) -> dict[tuple[int, str], np.ndarray]:
    collected: dict[tuple[int, str], list[np.ndarray]] = {
        (layer, pool): [] for layer in LAYERS for pool in POOLS
    }
    for index, row in enumerate(rows, 1):
        tokens = mx.array(prompt_tokens(tokenizer, row["prompt"], raw_prompts), dtype=mx.int32)[None, :]
        h = model.model.embed_tokens(tokens)

        def record(layer: int, value: mx.array) -> None:
            for pool, vector in (
                ("last", value[0, -1]),
                ("mean", mx.mean(value[0], axis=0)),
            ):
                vector = vector.astype(mx.float32)
                mx.eval(vector)
                collected[(layer, pool)].append(np.array(vector, copy=True))

        record(0, h)
        mask = __import__("mlx_lm.models.base", fromlist=["create_attention_mask"]).create_attention_mask(h, None)
        for layer_index, layer in enumerate(model.model.layers, 1):
            h = layer(h, mask, None)
            if layer_index in LAYERS and layer_index != 28:
                record(layer_index, h)
        record(28, model.model.norm(h))
        if index % 50 == 0 or index == len(rows):
            print(f"features {index}/{len(rows)}", flush=True)
    return {key: np.stack(values) for key, values in collected.items()}


def labels(rows: list[dict], classes: list[str]) -> np.ndarray:
    index = {label: position for position, label in enumerate(classes)}
    return np.array([index[row.get("family", row.get("route"))] for row in rows], dtype=np.int64)


def fit_ridge(x: np.ndarray, y: np.ndarray, classes: int, ridge: float) -> dict[str, np.ndarray]:
    mean = x.mean(axis=0)
    scale = x.std(axis=0)
    scale[scale < 1e-5] = 1.0
    z = (x - mean) / scale
    targets = np.eye(classes, dtype=np.float32)[y]
    kernel = z @ z.T
    alpha = np.linalg.solve(kernel + ridge * np.eye(len(z), dtype=np.float32), targets)
    weights = z.T @ alpha
    return {"mean": mean, "scale": scale, "weights": weights}


def predict(model: dict[str, np.ndarray], x: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    scores = ((x - model["mean"]) / model["scale"]) @ model["weights"]
    return scores.argmax(axis=1), scores


def metrics(rows: list[dict], expected: np.ndarray, predicted: np.ndarray, classes: list[str]) -> dict:
    confusion = Counter((classes[int(gold)], classes[int(guess)]) for gold, guess in zip(expected, predicted))
    pair_groups: dict[str, list[bool]] = {}
    for row, gold, guess in zip(rows, expected, predicted):
        if row.get("pair_id"):
            pair_groups.setdefault(row["pair_id"], []).append(bool(gold == guess))
    return {
        "count": len(rows),
        "accuracy": float(np.mean(expected == predicted)),
        "pair_accuracy": (
            sum(len(values) == 2 and all(values) for values in pair_groups.values()) / len(pair_groups)
            if pair_groups else None
        ),
        "prediction_counts": dict(sorted(Counter(classes[int(value)] for value in predicted).items())),
        "confusion": [
            {"expected": gold, "predicted": guess, "count": count}
            for (gold, guess), count in sorted(confusion.items())
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", required=True)
    parser.add_argument("--weights", type=Path)
    parser.add_argument("--train", type=Path, required=True)
    parser.add_argument("--validation", type=Path, required=True)
    parser.add_argument("--contrast", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--fixed-layer", type=int, choices=LAYERS)
    parser.add_argument("--fixed-pool", choices=POOLS)
    parser.add_argument("--fixed-ridge", type=float, choices=RIDGES)
    parser.add_argument("--seal-only", action="store_true")
    parser.add_argument("--raw-prompts", action="store_true")
    args = parser.parse_args()

    started = time.time()
    train_rows = read_jsonl(args.train)
    validation_rows = read_jsonl(args.validation)
    classes = sorted({row["family"] for row in train_rows})
    model, tokenizer = load(args.model, tokenizer_config={"trust_remote_code": True})
    if args.weights is not None:
        model.load_weights(list(mx.load(str(args.weights)).items()), strict=True)
    model.freeze()

    # Extract and select without opening the matched contrast set.
    train_features = extract(model, tokenizer, train_rows, args.raw_prompts)
    validation_features = extract(model, tokenizer, validation_rows, args.raw_prompts)
    y_train = labels(train_rows, classes)
    y_validation = labels(validation_rows, classes)
    trials: list[dict] = []
    fitted: dict[tuple[int, str, float], dict[str, np.ndarray]] = {}
    for layer in LAYERS:
        for pool in POOLS:
            for ridge in RIDGES:
                key = (layer, pool, ridge)
                probe = fit_ridge(train_features[(layer, pool)], y_train, len(classes), ridge)
                fitted[key] = probe
                train_prediction, _ = predict(probe, train_features[(layer, pool)])
                validation_prediction, _ = predict(probe, validation_features[(layer, pool)])
                trials.append(
                    {
                        "layer": layer,
                        "pool": pool,
                        "ridge": ridge,
                        "train_accuracy": float(np.mean(train_prediction == y_train)),
                        "validation_accuracy": float(np.mean(validation_prediction == y_validation)),
                    }
                )
    fixed = (args.fixed_layer, args.fixed_pool, args.fixed_ridge)
    if any(value is not None for value in fixed):
        if not all(value is not None for value in fixed):
            raise ValueError("fixed layer, pool, and ridge must be supplied together")
        selected = next(
            row for row in trials
            if (row["layer"], row["pool"], row["ridge"]) == fixed
        )
        selection_mode = "configuration fixed externally before held-out evaluation"
    else:
        selected = sorted(
            trials,
            key=lambda row: (-row["validation_accuracy"], -row["train_accuracy"], row["layer"], row["pool"], row["ridge"]),
        )[0]
        selection_mode = "highest paraphrase validation accuracy"
    selected_key = (selected["layer"], selected["pool"], selected["ridge"])
    probe = fitted[selected_key]

    args.output_dir.mkdir(parents=True, exist_ok=True)
    probe_path = args.output_dir / "probe.npz"
    np.savez(
        probe_path,
        mean=probe["mean"],
        scale=probe["scale"],
        weights=probe["weights"],
        classes=np.array(classes),
        layer=np.array(selected["layer"]),
        pool=np.array(selected["pool"]),
        ridge=np.array(selected["ridge"]),
    )
    seal = {
        "schema_version": 1,
        "selection_data": [str(args.train), str(args.validation)],
        "selection_data_sha256": [digest(args.train), digest(args.validation)],
        "contrast_opened": False,
        "classes": classes,
        "selected": selected,
        "selection_mode": selection_mode,
        "probe": str(probe_path),
        "probe_sha256": digest(probe_path),
        "probe_bytes": probe_path.stat().st_size,
        "trainable_parameters": int(probe["weights"].size),
    }
    seal_path = args.output_dir / "selection-seal.json"
    seal_path.write_text(json.dumps(seal, indent=2, sort_keys=True) + "\n")
    seal_hash = digest(seal_path)
    print(json.dumps({"selection_sealed": seal_hash, **seal}, indent=2, sort_keys=True), flush=True)

    if args.seal_only:
        return

    # Only now open the held-out matched contrast set.
    contrast_rows = read_jsonl(args.contrast)
    contrast_feature_sets = extract(model, tokenizer, contrast_rows, args.raw_prompts)
    contrast_features = contrast_feature_sets[(selected["layer"], selected["pool"])]
    y_contrast = labels(contrast_rows, classes)
    train_prediction, _ = predict(probe, train_features[(selected["layer"], selected["pool"])])
    validation_prediction, _ = predict(probe, validation_features[(selected["layer"], selected["pool"])])
    contrast_prediction, contrast_scores = predict(probe, contrast_features)
    posthoc_contrast_trials = []
    for trial in trials:
        key = (trial["layer"], trial["pool"], trial["ridge"])
        trial_prediction, _ = predict(fitted[key], contrast_feature_sets[(trial["layer"], trial["pool"])])
        posthoc_contrast_trials.append(
            {
                **trial,
                "contrast_accuracy": float(np.mean(trial_prediction == y_contrast)),
            }
        )
    posthoc_contrast_trials.sort(
        key=lambda row: (-row["contrast_accuracy"], -row["validation_accuracy"], row["layer"], row["pool"], row["ridge"])
    )
    predictions_path = args.output_dir / "contrast-predictions.jsonl"
    with predictions_path.open("w", encoding="utf-8") as handle:
        for row, gold, guess, scores in zip(contrast_rows, y_contrast, contrast_prediction, contrast_scores):
            handle.write(
                json.dumps(
                    {
                        "id": row["id"],
                        "expected_route": classes[int(gold)],
                        "predicted_route": classes[int(guess)],
                        "correct": bool(gold == guess),
                        "pair_id": row.get("pair_id"),
                        "scores": {label: float(score) for label, score in zip(classes, scores)},
                    },
                    sort_keys=True,
                )
                + "\n"
            )
    report = {
        "schema_version": 1,
        "purpose": "test whether a tiny frozen readout can recover mathematical method concepts without modifying the language model",
        "input_contract": "natural-language statement only",
        "model": args.model,
        "weights": str(args.weights) if args.weights is not None else None,
        "weights_sha256": digest(args.weights) if args.weights is not None else None,
        "classes": classes,
        "selection_seal_sha256": seal_hash,
        "selected": selected,
        "probe_bytes": probe_path.stat().st_size,
        "trainable_parameters": int(probe["weights"].size),
        "train": metrics(train_rows, y_train, train_prediction, classes),
        "validation": metrics(validation_rows, y_validation, validation_prediction, classes),
        "contrast": metrics(contrast_rows, y_contrast, contrast_prediction, classes),
        "posthoc_oracle_best_contrast_trial": posthoc_contrast_trials[0],
        "posthoc_oracle_warning": "Uses held-out contrast labels after unsealing and is diagnostic only; it is not a selectable result.",
        "all_trials": posthoc_contrast_trials,
        "contrast_sha256": digest(args.contrast),
        "predictions_sha256": digest(predictions_path),
        "elapsed_seconds": time.time() - started,
        "limitations": [
            "This measures closed-set method selection, not method execution or proof generation.",
            "The linear head uses labeled method-routing examples even though the language model remains frozen.",
            "The synthetic five-family contrast set does not establish broad mathematical abstraction.",
        ],
    }
    report_path = args.output_dir / "report.json"
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
