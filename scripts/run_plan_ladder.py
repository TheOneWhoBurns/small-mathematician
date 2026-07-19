#!/usr/bin/env python3
"""Generate natural-language plans for a verified-plan ladder split."""

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
    parser.add_argument(
        "--quantized-delta",
        help="Optional int8 delta from --weights, produced by quantize_checkpoint_delta.py.",
    )
    parser.add_argument("--adapter-path")
    parser.add_argument("--prompts", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--max-tokens", type=int, default=256)
    parser.add_argument("--temperature", type=float, default=0.0)
    parser.add_argument("--seed", type=int, default=17)
    parser.add_argument("--prompt-prefix", default="Respond only in English.\n")
    parser.add_argument("--prompt-suffix", default="\nPlan:\n")
    parser.add_argument(
        "--chat-template",
        action="store_true",
        help="Wrap the natural-language prompt in the model's user/assistant template.",
    )
    parser.add_argument(
        "--assistant-prefix",
        default="",
        help="Optional decoded assistant prefix for exposure-bias diagnostics.",
    )
    parser.add_argument("--limit", type=int)
    parser.add_argument("--family", help="Generate only rows with this public family label.")
    parser.add_argument("--deadline")
    args = parser.parse_args()

    rows = [
        json.loads(line)
        for line in args.prompts.read_text().splitlines()
        if line.strip()
    ]
    if args.family is not None:
        rows = [
            row
            for row in rows
            if row.get("family", row.get("metadata", {}).get("family")) == args.family
        ]
    if args.limit is not None:
        rows = rows[: args.limit]

    completed: set[str] = set()
    if args.output.exists():
        completed = {
            json.loads(line)["id"]
            for line in args.output.read_text().splitlines()
            if line.strip()
        }

    model, tokenizer = load(
        args.model,
        tokenizer_config={"trust_remote_code": True},
        adapter_path=args.adapter_path,
    )
    if args.quantized_delta and not args.weights:
        parser.error("--quantized-delta requires --weights")
    if args.weights:
        weights = mx.load(args.weights)
        if args.quantized_delta:
            delta = mx.load(args.quantized_delta)
            for name in list(weights):
                quantized = delta[name + ".__delta_q"]
                scale = delta[name + ".__delta_scale"]
                weights[name] = weights[name] + quantized.astype(weights[name].dtype) * scale.astype(weights[name].dtype)
        model.load_weights(list(weights.items()), strict=True)
    sampler = make_sampler(temp=args.temperature)
    mx.random.seed(args.seed)
    deadline = datetime.fromisoformat(args.deadline) if args.deadline else None

    args.output.parent.mkdir(parents=True, exist_ok=True)
    started = time.time()
    generated = 0
    with args.output.open("a", encoding="utf-8") as handle:
        for index, row in enumerate(rows, 1):
            example_id = row.get(
                "id",
                row.get("semantic_instance_id", row.get("metadata", {}).get("id")),
            )
            if not isinstance(example_id, str):
                raise ValueError("every prompt row needs string id or semantic_instance_id")
            if example_id in completed:
                continue
            if deadline and datetime.now(deadline.tzinfo) >= deadline:
                break
            prompt_text = row.get("prompt", row.get("text"))
            if not isinstance(prompt_text, str):
                raise ValueError(f"prompt row {example_id} has no string prompt")
            prompt = args.prompt_prefix + prompt_text.rstrip() + args.prompt_suffix
            if args.chat_template:
                prompt = tokenizer.apply_chat_template(
                    [{"role": "user", "content": prompt}],
                    add_generation_prompt=True,
                    tokenize=False,
                )
            prompt += args.assistant_prefix
            response = generate(
                model,
                tokenizer,
                prompt=prompt,
                max_tokens=args.max_tokens,
                sampler=sampler,
                verbose=False,
            )
            response = response.split("<|im_end|>", 1)[0].split("<|endoftext|>", 1)[0].strip()
            record = {"id": example_id, "response": response}
            handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")
            handle.flush()
            generated += 1
            print(f"{index}/{len(rows)} {example_id}", flush=True)

    elapsed = time.time() - started
    manifest = {
        "schema_version": 1,
        "created_unix": time.time(),
        "elapsed_seconds": elapsed,
        "prompts_per_second": generated / elapsed if elapsed else None,
        "peak_metal_gb": mx.get_peak_memory() / 1e9,
        "model": args.model,
        "weights": args.weights,
        "weights_sha256": sha256(Path(args.weights)) if args.weights else None,
        "quantized_delta": args.quantized_delta,
        "quantized_delta_sha256": sha256(Path(args.quantized_delta)) if args.quantized_delta else None,
        "adapter_path": args.adapter_path,
        "adapter_sha256": (
            sha256(Path(args.adapter_path) / "adapters.safetensors")
            if args.adapter_path
            else None
        ),
        "prompts": str(args.prompts),
        "prompts_sha256": sha256(args.prompts),
        "output": str(args.output),
        "max_tokens": args.max_tokens,
        "temperature": args.temperature,
        "seed": args.seed,
        "prompt_prefix": args.prompt_prefix,
        "prompt_suffix": args.prompt_suffix,
        "chat_template": args.chat_template,
        "assistant_prefix": args.assistant_prefix,
        "requested": len(rows),
        "family": args.family,
        "new_predictions": generated,
        "predictions_total": sum(
            1 for line in args.output.read_text().splitlines() if line.strip()
        ),
        "deadline": args.deadline,
    }
    args.output.with_suffix(args.output.suffix + ".manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
