#!/usr/bin/env python3
"""Generate a predeclared candidate set for verifier-guided atomic rejection."""

from __future__ import annotations

import argparse
import hashlib
import json
import time
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
    parser.add_argument("--weights", type=Path, required=True)
    parser.add_argument("--prompts", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--max-tokens", type=int, default=64)
    args = parser.parse_args()

    configs = [(temperature, seed) for temperature in (0.4, 0.8) for seed in (17, 23, 31, 47)]
    prompts = [json.loads(line) for line in args.prompts.read_text(encoding="utf-8").splitlines() if line.strip()]
    model, tokenizer = load(args.model, tokenizer_config={"trust_remote_code": True})
    model.load_weights(str(args.weights), strict=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    started = time.time()
    with args.output.open("w", encoding="utf-8") as handle:
        for prompt_index, row in enumerate(prompts):
            for sample_index, (temperature, seed) in enumerate(configs):
                mx.random.seed(seed + prompt_index * 1009)
                response = generate(
                    model,
                    tokenizer,
                    prompt=row["prompt"],
                    max_tokens=args.max_tokens,
                    sampler=make_sampler(temp=temperature),
                    verbose=False,
                )
                response = response.split("<|im_end|>", 1)[0].split("<|endoftext|>", 1)[0].strip()
                handle.write(json.dumps({"id": row["id"], "sample_index": sample_index, "temperature": temperature, "seed": seed, "response": response}, sort_keys=True) + "\n")
            print(f"{prompt_index + 1}/{len(prompts)} {row['id']}", flush=True)
    manifest = {
        "count_prompts": len(prompts),
        "candidates_per_prompt": len(configs),
        "candidate_count": len(prompts) * len(configs),
        "configs": [{"temperature": temperature, "seed": seed} for temperature, seed in configs],
        "elapsed_seconds": time.time() - started,
        "peak_metal_gb": mx.get_peak_memory() / 1e9,
        "prompts_sha256": sha256(args.prompts),
        "weights_sha256": sha256(args.weights),
        "candidates_sha256": sha256(args.output),
    }
    args.output.with_suffix(".manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
