#!/usr/bin/env python3
"""Build deterministic timing fixtures from candidate data, never eval data."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from transformers import AutoTokenizer


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", required=True)
    parser.add_argument("--candidates-dir", required=True)
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--target-tokens", type=int, nargs="+", required=True)
    parser.add_argument("--train-rows", type=int, default=12)
    parser.add_argument("--valid-rows", type=int, default=3)
    parser.add_argument("--test-rows", type=int, default=3)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    tokenizer = AutoTokenizer.from_pretrained(args.model, trust_remote_code=True)
    candidates_dir = Path(args.candidates_dir)
    rows: list[dict] = []
    for source in ("naturalproofs.jsonl", "fineproofs.jsonl"):
        with (candidates_dir / source).open() as handle:
            for line in handle:
                row = json.loads(line)
                prompt = "Problem: " + row["statement"].strip() + "\n"
                labels = "; ".join(row.get("concept_labels", []))
                completion = (
                    "Relevant concepts: "
                    + labels
                    + "\nProof blueprint: "
                    + row["argument"].strip()
                )
                token_count = len(
                    tokenizer(
                        prompt + completion,
                        add_special_tokens=True,
                    )["input_ids"]
                )
                rows.append(
                    {
                        "prompt": prompt,
                        "completion": completion,
                        "probe_metadata": {
                            "id": row["id"],
                            "source": source.removesuffix(".jsonl"),
                            "tokens": token_count,
                        },
                    }
                )

    wanted = args.train_rows + args.valid_rows + args.test_rows
    offsets = {
        "train": (0, args.train_rows),
        "valid": (args.train_rows, args.train_rows + args.valid_rows),
        "test": (args.train_rows + args.valid_rows, wanted),
    }
    for target in args.target_tokens:
        ranked = sorted(
            rows,
            key=lambda row: (
                abs(row["probe_metadata"]["tokens"] - target),
                row["probe_metadata"]["id"],
            ),
        )
        selected = ranked[:wanted]
        output_dir = Path(args.output_dir) / f"tokens-{target}"
        output_dir.mkdir(parents=True, exist_ok=True)
        for split, (start, end) in offsets.items():
            with (output_dir / f"{split}.jsonl").open("w") as handle:
                for row in selected[start:end]:
                    handle.write(json.dumps(row, ensure_ascii=False) + "\n")

        manifest = {
            "schema_version": 1,
            "candidate_sources": ["naturalproofs", "fineproofs"],
            "eval_sources_read": [],
            "target_tokens": target,
            "selected_token_counts": [r["probe_metadata"]["tokens"] for r in selected],
            "splits": {name: end - start for name, (start, end) in offsets.items()},
        }
        (output_dir / "manifest.json").write_text(
            json.dumps(manifest, indent=2, sort_keys=True) + "\n"
        )
        print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
