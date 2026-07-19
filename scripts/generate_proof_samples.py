#!/usr/bin/env python3
"""Generate natural-language proofs for a deterministic slice of a training view."""

from __future__ import annotations

import argparse
import hashlib
import json
import time
from datetime import datetime
from pathlib import Path

import mlx.core as mx
from mlx_lm import generate
from mlx_lm.sample_utils import make_sampler
from mlx_lm.utils import load


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", required=True)
    parser.add_argument("--weights")
    parser.add_argument("--view", type=Path, required=True)
    parser.add_argument("--split", choices=("valid", "test"), default="valid")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--limit", type=int, default=8)
    parser.add_argument("--offset", type=int, default=0)
    parser.add_argument("--max-tokens", type=int, default=400)
    parser.add_argument("--temperature", type=float, default=0.0)
    parser.add_argument("--seed", type=int, default=17)
    parser.add_argument("--deadline")
    parser.add_argument("--task", choices=("proof", "blueprint"), default="proof")
    parser.add_argument("--blueprint-max-words", type=int)
    args = parser.parse_args()
    if args.offset < 0:
        parser.error("--offset must be non-negative")
    if args.blueprint_max_words is not None and args.blueprint_max_words < 1:
        parser.error("--blueprint-max-words must be positive")

    source = args.view / f"{args.split}.jsonl"
    rows = [json.loads(line) for line in source.read_text().splitlines() if line.strip()]
    rows.sort(key=lambda row: hashlib.sha256(f"proof-sample-v1|{row['metadata']['family_id']}".encode()).hexdigest())
    rows = rows[args.offset : args.offset + args.limit]
    completed = set()
    if args.output.exists():
        completed = {
            json.loads(line)["id"]
            for line in args.output.read_text().splitlines()
            if line.strip()
        }

    model, tokenizer = load(args.model, tokenizer_config={"trust_remote_code": True})
    if args.weights:
        weights = mx.load(args.weights)
        model.load_weights(list(weights.items()), strict=True)
    sampler = make_sampler(temp=args.temperature)
    mx.random.seed(args.seed)
    deadline = datetime.fromisoformat(args.deadline) if args.deadline else None
    args.output.parent.mkdir(parents=True, exist_ok=True)
    started = time.time()
    new_predictions = 0
    with args.output.open("a", encoding="utf-8") as handle:
        for index, row in enumerate(rows, 1):
            example_id = row["metadata"]["id"]
            if example_id in completed:
                continue
            if deadline and datetime.now(deadline.tzinfo) >= deadline:
                break
            prompt = row["prompt"].rstrip()
            if args.task == "blueprint":
                instruction = "Provide a correct natural-language proof or solution."
                if prompt.endswith(instruction):
                    prompt = prompt[: -len(instruction)].rstrip()
                prompt += (
                    "\nProvide a concise natural-language proof blueprint: state the central "
                    "idea and the necessary logical steps."
                )
                if args.blueprint_max_words is not None:
                    prompt += f" Use no more than {args.blueprint_max_words} words."
            prompt += "\nSolution:\n"
            response = generate(
                model,
                tokenizer,
                prompt=prompt,
                max_tokens=args.max_tokens,
                sampler=sampler,
                verbose=False,
            )
            response = response.split("<|im_end|>", 1)[0].split("<|endoftext|>", 1)[0].strip()
            handle.write(
                json.dumps(
                    {
                        "id": example_id,
                        "family_id": row["metadata"]["family_id"],
                        "domain": row["metadata"]["domain"],
                        "prompt": row["prompt"],
                        "response": response,
                    },
                    ensure_ascii=False,
                )
                + "\n"
            )
            handle.flush()
            new_predictions += 1
            print(f"{index}/{len(rows)} {example_id}", flush=True)

    manifest = {
        "schema_version": 1,
        "created_unix": time.time(),
        "elapsed_seconds": time.time() - started,
        "model": args.model,
        "weights": args.weights,
        "weights_sha256": sha256(Path(args.weights)) if args.weights else None,
        "view": str(args.view),
        "source_sha256": sha256(source),
        "split": args.split,
        "selection": "rows by sha256('proof-sample-v1|' + family_id), then offset/limit",
        "offset": args.offset,
        "limit": args.limit,
        "max_tokens": args.max_tokens,
        "temperature": args.temperature,
        "seed": args.seed,
        "task": args.task,
        "blueprint_max_words": args.blueprint_max_words,
        "new_predictions": new_predictions,
    }
    args.output.with_suffix(args.output.suffix + ".manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
