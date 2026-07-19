#!/usr/bin/env python3
"""Dependency-free word/character TF-IDF nearest-centroid routing baseline."""

from __future__ import annotations

import argparse
import json
import math
import re
from collections import Counter, defaultdict
from pathlib import Path


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def features(text: str) -> Counter[str]:
    normalized = " ".join(re.findall(r"[a-z0-9]+", text.lower()))
    words = normalized.split()
    result: Counter[str] = Counter()
    for size in (1, 2):
        result.update("w:" + " ".join(words[index:index + size]) for index in range(len(words) - size + 1))
    padded = " " + normalized + " "
    for size in (3, 4, 5):
        result.update("c:" + padded[index:index + size] for index in range(len(padded) - size + 1))
    return result


def normalize(vector: dict[str, float]) -> dict[str, float]:
    norm = math.sqrt(sum(value * value for value in vector.values()))
    return {key: value / norm for key, value in vector.items()} if norm else {}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--train", type=Path, required=True)
    parser.add_argument("--test", type=Path, required=True)
    parser.add_argument("--predictions-out", type=Path)
    args = parser.parse_args()

    train = read_jsonl(args.train)
    test = read_jsonl(args.test)
    train_counts = [features(row["prompt"]) for row in train]
    document_frequency: Counter[str] = Counter()
    for counts in train_counts:
        document_frequency.update(counts.keys())
    idf = {
        feature: math.log((1 + len(train)) / (1 + frequency)) + 1
        for feature, frequency in document_frequency.items()
    }

    centroids: dict[str, defaultdict[str, float]] = defaultdict(lambda: defaultdict(float))
    family_counts: Counter[str] = Counter()
    for row, counts in zip(train, train_counts, strict=True):
        vector = normalize({key: value * idf[key] for key, value in counts.items()})
        for key, value in vector.items():
            centroids[row["family"]][key] += value
        family_counts[row["family"]] += 1
    normalized_centroids = {
        family: normalize({key: value / family_counts[family] for key, value in values.items()})
        for family, values in centroids.items()
    }

    confusion: Counter[tuple[str, str]] = Counter()
    correct = 0
    predictions = []
    for row in test:
        counts = features(row["prompt"])
        vector = normalize({key: value * idf[key] for key, value in counts.items() if key in idf})
        scores = {
            family: sum(value * centroid.get(key, 0.0) for key, value in vector.items())
            for family, centroid in normalized_centroids.items()
        }
        predicted = max(scores, key=scores.get)
        confusion[(row["family"], predicted)] += 1
        correct += predicted == row["family"]
        predictions.append(
            {
                "id": row["id"],
                "expected_route": row["family"],
                "predicted_route": predicted,
                "correct": predicted == row["family"],
                "pair_id": row.get("pair_id"),
                "scores": scores,
            }
        )
    if args.predictions_out is not None:
        args.predictions_out.parent.mkdir(parents=True, exist_ok=True)
        with args.predictions_out.open("w", encoding="utf-8") as handle:
            for row in predictions:
                handle.write(json.dumps(row, sort_keys=True) + "\n")
    report = {
        "baseline": "word-1/2gram plus character-3/4/5gram TF-IDF nearest centroid",
        "train_count": len(train),
        "test_count": len(test),
        "accuracy": correct / len(test),
        "confusion": [
            {"expected": expected, "predicted": predicted, "count": count}
            for (expected, predicted), count in sorted(confusion.items())
        ],
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
