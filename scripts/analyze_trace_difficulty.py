#!/usr/bin/env python3
"""Cross-validated diagnostic for magnitude, chain, and local-division difficulty."""

from __future__ import annotations

import argparse
import json
import math
import random
import re
from collections import defaultdict
from pathlib import Path

import numpy as np


STEP = re.compile(r"Euclidean step: (-?\d+) = (-?\d+) times (-?\d+) plus (-?\d+)\.")


def load(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def sigmoid(value: np.ndarray) -> np.ndarray:
    value = np.clip(value, -30, 30)
    return 1.0 / (1.0 + np.exp(-value))


def fit_logistic(x: np.ndarray, y: np.ndarray, ridge: float = 1.0) -> np.ndarray:
    weights = np.zeros(x.shape[1], dtype=np.float64)
    penalty = np.eye(x.shape[1], dtype=np.float64) * ridge
    penalty[0, 0] = 0.0
    for _ in range(100):
        probabilities = sigmoid(x @ weights)
        variance = np.maximum(probabilities * (1.0 - probabilities), 1e-6)
        gradient = x.T @ (probabilities - y) + penalty @ weights
        hessian = (x.T * variance) @ x + penalty
        update = np.linalg.solve(hessian, gradient)
        weights -= update
        if np.max(np.abs(update)) < 1e-8:
            break
    return weights


def auc(y: np.ndarray, p: np.ndarray) -> float:
    positives = np.flatnonzero(y == 1)
    negatives = np.flatnonzero(y == 0)
    if not len(positives) or not len(negatives):
        return float("nan")
    wins = sum(float(p[i] > p[j]) + 0.5 * float(p[i] == p[j]) for i in positives for j in negatives)
    return wins / (len(positives) * len(negatives))


def cross_validate(features: np.ndarray, y: np.ndarray, folds: list[np.ndarray]) -> dict:
    probabilities = np.zeros(len(y), dtype=np.float64)
    for test in folds:
        train = np.setdiff1d(np.arange(len(y)), test)
        mean = features[train].mean(axis=0)
        scale = features[train].std(axis=0)
        scale[scale < 1e-8] = 1.0
        train_x = np.column_stack([np.ones(len(train)), (features[train] - mean) / scale])
        test_x = np.column_stack([np.ones(len(test)), (features[test] - mean) / scale])
        weights = fit_logistic(train_x, y[train])
        probabilities[test] = sigmoid(test_x @ weights)
    clipped = np.clip(probabilities, 1e-8, 1 - 1e-8)
    return {
        "log_loss": float(-np.mean(y * np.log(clipped) + (1 - y) * np.log(1 - clipped))),
        "brier": float(np.mean((probabilities - y) ** 2)),
        "auc": float(auc(y, probabilities)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--verifier", type=Path, required=True)
    parser.add_argument("--details", type=Path, required=True)
    parser.add_argument("--metric", choices=("trace_valid", "semantic"), default="trace_valid")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    private = {row["id"]: row for row in load(args.verifier)}
    evaluated = {row["id"]: row for row in load(args.details)}
    if private.keys() != evaluated.keys():
        raise ValueError("IDs differ")

    rows = []
    for identifier, row in private.items():
        a, b = row["parameters"]["a"], row["parameters"]["b"]
        steps = [tuple(map(int, match)) for match in STEP.findall(row["expected"])]
        quotients = [step[1] for step in steps]
        rows.append(
            {
                "id": identifier,
                "surface": row["surface"],
                "magnitude_log10": math.log10(max(a, b)),
                "digits": len(str(max(a, b))),
                "steps": len(steps),
                "max_quotient_log1p": math.log1p(max(quotients)),
                "mean_quotient_log1p": sum(math.log1p(value) for value in quotients) / len(quotients),
                "valid": int(evaluated[identifier][args.metric]),
            }
        )
    names = ["magnitude_log10", "digits", "steps", "max_quotient_log1p", "mean_quotient_log1p"]
    matrix = np.array([[row[name] for name in names] for row in rows], dtype=np.float64)
    y = np.array([row["valid"] for row in rows], dtype=np.float64)
    rng = random.Random(20260827)
    grouped_indices: dict[str, list[int]] = defaultdict(list)
    for index, row in enumerate(rows):
        grouped_indices[row["surface"]].append(index)
    fold_lists = [[] for _ in range(5)]
    for indices in grouped_indices.values():
        rng.shuffle(indices)
        for offset, index in enumerate(indices):
            fold_lists[offset % 5].append(index)
    folds = [np.array(sorted(items), dtype=np.int64) for items in fold_lists]
    specifications = {
        "constant": [],
        "magnitude": [0, 1],
        "chain": [2],
        "local_quotient": [3, 4],
        "magnitude_plus_chain": [0, 1, 2],
        "all": [0, 1, 2, 3, 4],
    }
    models = {}
    for label, columns in specifications.items():
        selected = matrix[:, columns] if columns else np.zeros((len(rows), 1))
        models[label] = {"features": [names[index] for index in columns], **cross_validate(selected, y, folds)}
    surfaces = {}
    for surface in sorted(grouped_indices):
        values = [rows[index]["valid"] for index in grouped_indices[surface]]
        surfaces[surface] = {"count": len(values), "valid": sum(values), "rate": sum(values) / len(values)}
    report = {"count": len(rows), "metric": args.metric, "overall_rate": float(y.mean()), "per_surface": surfaces, "five_fold_cross_validation": models}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
