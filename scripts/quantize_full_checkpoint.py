#!/usr/bin/env python3
"""Quantize a standalone full-parameter MLX checkpoint reproducibly."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import mlx.core as mx
from mlx_lm.convert import quantize_model, save
from mlx_lm.utils import load


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", required=True)
    parser.add_argument("--weights", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--bits", type=int, choices=(4, 6, 8), required=True)
    parser.add_argument("--group-size", type=int, default=64)
    args = parser.parse_args()
    if args.output_dir.exists():
        raise ValueError(f"output directory already exists: {args.output_dir}")

    model, tokenizer, config = load(
        args.model,
        tokenizer_config={"trust_remote_code": True},
        return_config=True,
        lazy=True,
    )
    weights = mx.load(str(args.weights))
    model.load_weights(list(weights.items()), strict=True)
    mx.eval(model.parameters())
    model, config = quantize_model(
        model,
        config,
        group_size=args.group_size,
        bits=args.bits,
        mode="affine",
    )
    save(args.output_dir, args.model, model, tokenizer, config)

    weight_files = sorted(args.output_dir.glob("*.safetensors"))
    manifest = {
        "schema_version": 1,
        "base_model": args.model,
        "source_weights": str(args.weights),
        "source_weights_sha256": sha256(args.weights),
        "bits": args.bits,
        "group_size": args.group_size,
        "quantization_mode": "affine",
        "weight_files": [
            {"path": path.name, "bytes": path.stat().st_size, "sha256": sha256(path)}
            for path in weight_files
        ],
        "total_weight_bytes": sum(path.stat().st_size for path in weight_files),
    }
    (args.output_dir / "quantization_manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
