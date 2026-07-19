#!/usr/bin/env python3
"""Create a deterministically randomized proof-quality judging packet."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def read_predictions(path: Path) -> dict[str, dict]:
    return {
        row["id"]: row
        for row in (json.loads(line) for line in path.read_text().splitlines() if line.strip())
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--view", type=Path, required=True)
    parser.add_argument("--base", type=Path, required=True)
    parser.add_argument("--incumbent", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--key", type=Path, required=True)
    args = parser.parse_args()

    sources = {
        "base": read_predictions(args.base),
        "incumbent": read_predictions(args.incumbent),
        "candidate": read_predictions(args.candidate),
    }
    ids = set.intersection(*(set(rows) for rows in sources.values()))
    references = {
        row["metadata"]["id"]: row
        for row in (
            json.loads(line)
            for line in (args.view / "valid.jsonl").read_text().splitlines()
            if line.strip()
        )
    }
    packet_rows = []
    key_rows = []
    for example_id in sorted(ids):
        ranked_models = sorted(
            sources,
            key=lambda model: hashlib.sha256(f"blind-proof-v1|{example_id}|{model}".encode()).hexdigest(),
        )
        labels = {model: chr(ord("A") + index) for index, model in enumerate(ranked_models)}
        packet_rows.append(
            {
                "id": example_id,
                "prompt": references[example_id]["prompt"],
                "reference": references[example_id]["completion"],
                "candidates": [
                    {"label": labels[model], "response": sources[model][example_id]["response"]}
                    for model in ranked_models
                ],
            }
        )
        key_rows.append({"id": example_id, "labels": {label: model for model, label in labels.items()}})

    for path, rows in ((args.packet, packet_rows), (args.key, key_rows)):
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("w", encoding="utf-8") as handle:
            for row in rows:
                handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
    print(json.dumps({"examples": len(packet_rows), "packet": str(args.packet), "key": str(args.key)}))


if __name__ == "__main__":
    main()
