#!/usr/bin/env python3
"""Evaluate completion loss for a base or literal full-weight checkpoint."""

from __future__ import annotations

import argparse
import json
import platform
import time
from importlib.metadata import version
from pathlib import Path
from types import SimpleNamespace

import mlx.core as mx
from mlx_lm.tuner.datasets import CacheDataset, load_dataset
from mlx_lm.tuner.trainer import evaluate
from mlx_lm.utils import load


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", required=True)
    parser.add_argument("--weights", help="Optional full weights.safetensors produced by train_all_parameters.py")
    parser.add_argument("--data", required=True)
    parser.add_argument("--split", choices=("valid", "test"), default="valid")
    parser.add_argument("--batch-size", type=int, default=1)
    parser.add_argument("--num-batches", type=int, default=-1)
    parser.add_argument("--max-seq-length", type=int, default=1024)
    parser.add_argument("--mask-prompt", action="store_true")
    parser.add_argument("--output", type=Path)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    model, tokenizer = load(args.model, tokenizer_config={"trust_remote_code": True})
    if args.weights:
        weights = mx.load(args.weights)
        model.load_weights(list(weights.items()), strict=True)

    dataset_args = SimpleNamespace(
        data=args.data,
        train=False,
        test=args.split == "test",
        mask_prompt=args.mask_prompt,
    )
    _train, valid, test = load_dataset(dataset_args, tokenizer)
    dataset = test if args.split == "test" else valid
    loss = evaluate(
        model,
        CacheDataset(dataset),
        batch_size=args.batch_size,
        num_batches=args.num_batches,
        max_seq_length=args.max_seq_length,
    )
    result = {
        "schema_version": 1,
        "created_unix": time.time(),
        "python": platform.python_version(),
        "mlx": version("mlx"),
        "mlx_lm": version("mlx-lm"),
        "model": args.model,
        "weights": args.weights,
        "data": args.data,
        "split": args.split,
        "examples": len(dataset),
        "num_batches": args.num_batches,
        "max_seq_length": args.max_seq_length,
        "mask_prompt": args.mask_prompt,
        "loss": loss,
        "perplexity": float(mx.exp(mx.array(loss)).item()),
    }
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
