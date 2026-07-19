#!/usr/bin/env python3
"""Linearly interpolate two full MLX safetensors checkpoints."""

from __future__ import annotations

import argparse
import hashlib
import json
import time
from pathlib import Path

import mlx.core as mx


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--checkpoint-a", type=Path, required=True)
    parser.add_argument("--checkpoint-b", type=Path, required=True)
    parser.add_argument("--alpha", type=float, required=True, help="0 gives A; 1 gives B")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not 0.0 <= args.alpha <= 1.0:
        raise ValueError("alpha must be between 0 and 1")
    for path in (args.checkpoint_a, args.checkpoint_b):
        if not path.is_file():
            raise FileNotFoundError(path)

    weights_a = mx.load(str(args.checkpoint_a))
    weights_b = mx.load(str(args.checkpoint_b))
    if set(weights_a) != set(weights_b):
        only_a = sorted(set(weights_a) - set(weights_b))[:5]
        only_b = sorted(set(weights_b) - set(weights_a))[:5]
        raise ValueError(f"checkpoint keys differ; only A={only_a}, only B={only_b}")

    mixed = {}
    for name in sorted(weights_a):
        left, right = weights_a[name], weights_b[name]
        if left.shape != right.shape:
            raise ValueError(f"shape mismatch for {name}: {left.shape} versus {right.shape}")
        if left.dtype != right.dtype:
            raise ValueError(f"dtype mismatch for {name}: {left.dtype} versus {right.dtype}")
        mixed[name] = (
            left.astype(mx.float32) * (1.0 - args.alpha)
            + right.astype(mx.float32) * args.alpha
        ).astype(left.dtype)

    args.output.parent.mkdir(parents=True, exist_ok=True)
    mx.save_safetensors(str(args.output), mixed)
    mx.eval(*mixed.values())
    manifest = {
        "schema_version": 1,
        "created_unix": time.time(),
        "operation": "linear checkpoint interpolation",
        "alpha": args.alpha,
        "checkpoint_a": str(args.checkpoint_a),
        "checkpoint_a_sha256": sha256(args.checkpoint_a),
        "checkpoint_b": str(args.checkpoint_b),
        "checkpoint_b_sha256": sha256(args.checkpoint_b),
        "output": str(args.output),
        "output_sha256": sha256(args.output),
        "tensor_count": len(mixed),
    }
    args.output.with_suffix(".json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
