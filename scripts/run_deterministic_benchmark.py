#!/usr/bin/env python3
"""Run a local base or full-weight model on the deterministic NL benchmark."""

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


ROOT = Path(__file__).resolve().parents[1]
BENCHMARK = ROOT / "benchmarks" / "deterministic_nl" / "data"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", required=True)
    parser.add_argument("--weights", help="Optional literal full-model weights")
    parser.add_argument("--split", choices=("dev", "test"), required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--max-tokens", type=int, default=160)
    parser.add_argument("--temperature", type=float, default=0.0)
    parser.add_argument("--prompt-mode", choices=("chat", "raw"), default="chat")
    parser.add_argument("--system-prompt")
    parser.add_argument("--user-prefix", default="")
    parser.add_argument("--user-suffix", default="\nAnswer:\n")
    parser.add_argument("--seed", type=int, default=17)
    parser.add_argument("--limit", type=int)
    parser.add_argument("--deadline", help="ISO timestamp; stop before starting another item")
    return parser.parse_args()


def file_hash(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    args = parse_args()
    prompt_path = BENCHMARK / f"{args.split}.prompts.jsonl"
    prompts = [json.loads(line) for line in prompt_path.read_text().splitlines() if line.strip()]
    if args.limit is not None:
        prompts = prompts[: args.limit]
    deadline = datetime.fromisoformat(args.deadline) if args.deadline else None

    completed: set[str] = set()
    if args.output.exists():
        for line in args.output.read_text().splitlines():
            if line.strip():
                completed.add(json.loads(line)["id"])

    model, tokenizer = load(args.model, tokenizer_config={"trust_remote_code": True})
    if args.weights:
        weights = mx.load(args.weights)
        model.load_weights(list(weights.items()), strict=True)
    sampler = make_sampler(temp=args.temperature)
    mx.random.seed(args.seed)

    args.output.parent.mkdir(parents=True, exist_ok=True)
    started = time.time()
    generated_count = 0
    with args.output.open("a", encoding="utf-8") as handle:
        for index, row in enumerate(prompts, start=1):
            if row["id"] in completed:
                continue
            if deadline and datetime.now(deadline.tzinfo) >= deadline:
                print(f"deadline reached after {generated_count} new predictions", flush=True)
                break
            user_text = args.user_prefix + "Problem: " + row["prompt"] + args.user_suffix
            if args.prompt_mode == "chat":
                messages = []
                if args.system_prompt:
                    messages.append({"role": "system", "content": args.system_prompt})
                messages.append({"role": "user", "content": user_text})
                prompt = tokenizer.apply_chat_template(
                    messages,
                    add_generation_prompt=True,
                    return_dict=False,
                )
            else:
                prompt = user_text
            response = generate(
                model,
                tokenizer,
                prompt=prompt,
                max_tokens=args.max_tokens,
                sampler=sampler,
                verbose=False,
            )
            # Qwen base checkpoints can decode a chat stop token as visible text.
            # Treat it as a stop boundary before passing natural language onward.
            response = response.split("<|im_end|>", 1)[0].split("<|endoftext|>", 1)[0].strip()
            record = {"id": row["id"], "response": response}
            handle.write(json.dumps(record, ensure_ascii=False) + "\n")
            handle.flush()
            generated_count += 1
            print(f"{index}/{len(prompts)} {row['family']} {row['id']}", flush=True)

    manifest = {
        "schema_version": 1,
        "created_unix": time.time(),
        "elapsed_seconds": time.time() - started,
        "model": args.model,
        "weights": args.weights,
        "weights_sha256": file_hash(Path(args.weights)) if args.weights else None,
        "prompt_path": str(prompt_path.relative_to(ROOT)),
        "prompt_sha256": file_hash(prompt_path),
        "split": args.split,
        "max_tokens": args.max_tokens,
        "temperature": args.temperature,
        "prompt_mode": args.prompt_mode,
        "system_prompt": args.system_prompt,
        "user_prefix": args.user_prefix,
        "user_suffix": args.user_suffix,
        "seed": args.seed,
        "requested": len(prompts),
        "new_predictions": generated_count,
        "predictions_total": sum(1 for line in args.output.read_text().splitlines() if line.strip()),
        "deadline": args.deadline,
    }
    manifest_path = args.output.with_suffix(args.output.suffix + ".manifest.json")
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
