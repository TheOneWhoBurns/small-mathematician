#!/usr/bin/env python3
"""Store a target checkpoint as a per-tensor symmetric int8 delta."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import mlx.core as mx


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--base", type=Path, required=True)
    parser.add_argument("--target", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    base = mx.load(str(args.base))
    target = mx.load(str(args.target))
    if base.keys() != target.keys():
        raise ValueError("base and target checkpoint keys do not match")
    packed = {}
    zero_tensors = 0
    squared_error = 0.0
    squared_delta = 0.0
    for name in sorted(base):
        delta = (target[name].astype(mx.float32) - base[name].astype(mx.float32))
        maximum = float(mx.max(mx.abs(delta)).item())
        scale = maximum / 127.0 if maximum else 1.0
        quantized = mx.clip(mx.round(delta / scale), -127, 127).astype(mx.int8)
        restored = quantized.astype(mx.float32) * scale
        squared_error += float(mx.sum(mx.square(delta - restored)).item())
        squared_delta += float(mx.sum(mx.square(delta)).item())
        zero_tensors += int(maximum == 0.0)
        packed[name + ".__delta_q"] = quantized
        packed[name + ".__delta_scale"] = mx.array([scale], dtype=mx.float32)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    mx.save_safetensors(str(args.output), packed)
    report = {
        "schema_version": 1,
        "quantization": "symmetric per-tensor int8 delta",
        "base": str(args.base),
        "base_sha256": digest(args.base),
        "target": str(args.target),
        "target_sha256": digest(args.target),
        "output": str(args.output),
        "output_sha256": digest(args.output),
        "tensor_count": len(base),
        "zero_delta_tensors": zero_tensors,
        "relative_l2_error": (squared_error / squared_delta) ** 0.5 if squared_delta else 0.0,
    }
    args.output.with_suffix(".report.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
