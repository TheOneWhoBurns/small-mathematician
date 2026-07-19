#!/usr/bin/env python3
"""Train a compact raw-completion LoRA adapter on a quantized MLX model."""

from __future__ import annotations

import argparse
import json
import platform
import time
from importlib.metadata import version
from pathlib import Path

import mlx.core as mx
import mlx.optimizers as optim
import numpy as np
import mlx_lm.tuner.trainer as trainer_module
from mlx_lm.tuner.datasets import CacheDataset
from mlx_lm.tuner.trainer import TrainingArgs
from mlx_lm.tuner.utils import linear_to_lora_layers, print_trainable_parameters
from mlx_lm.utils import load


class RawCompletionsDataset:
    def __init__(self, rows, tokenizer):
        self._data = rows
        self.tokenizer = tokenizer

    def process(self, row):
        prompt_tokens = self.tokenizer.encode(row["prompt"])
        completion_tokens = self.tokenizer.encode(row["completion"])
        tokens = prompt_tokens + completion_tokens
        if tokens[-1] != self.tokenizer.eos_token_id:
            tokens.append(self.tokenizer.eos_token_id)
        return tokens, len(prompt_tokens)

    def __getitem__(self, index):
        return self._data[index]

    def __len__(self):
        return len(self._data)


def load_jsonl(path: Path):
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", required=True)
    parser.add_argument("--data", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--num-layers", type=int, default=-1)
    parser.add_argument("--rank", type=int, default=16)
    parser.add_argument("--scale", type=float, default=16.0)
    parser.add_argument("--dropout", type=float, default=0.0)
    parser.add_argument("--iters", type=int, default=300)
    parser.add_argument("--learning-rate", type=float, default=1e-4)
    parser.add_argument("--batch-size", type=int, default=1)
    parser.add_argument("--max-seq-length", type=int, default=512)
    parser.add_argument("--steps-per-report", type=int, default=50)
    parser.add_argument("--steps-per-eval", type=int, default=150)
    parser.add_argument("--val-batches", type=int, default=50)
    parser.add_argument("--save-every", type=int, default=150)
    parser.add_argument("--seed", type=int, default=53)
    parser.add_argument("--grad-checkpoint", action="store_true")
    args = parser.parse_args()

    np.random.seed(args.seed)
    mx.random.seed(args.seed)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    model, tokenizer = load(str(args.model), tokenizer_config={"trust_remote_code": True})
    train_set = RawCompletionsDataset(load_jsonl(args.data / "train.jsonl"), tokenizer)
    valid_set = RawCompletionsDataset(load_jsonl(args.data / "valid.jsonl"), tokenizer)

    model.freeze()
    lora_parameters = {"rank": args.rank, "scale": args.scale, "dropout": args.dropout}
    linear_to_lora_layers(model, args.num_layers, lora_parameters)
    print_trainable_parameters(model)

    adapter_file = args.output_dir / "adapters.safetensors"
    adapter_config = {
        "fine_tune_type": "lora",
        "num_layers": args.num_layers,
        "lora_parameters": lora_parameters,
    }
    (args.output_dir / "adapter_config.json").write_text(
        json.dumps(adapter_config, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    run_config = {
        "schema_version": 1,
        "created_unix": time.time(),
        "python": platform.python_version(),
        "mlx": version("mlx"),
        "mlx_lm": version("mlx-lm"),
        "device": mx.device_info(),
        "training_contract": "quantized backbone frozen; LoRA adapters only",
        "arguments": {key: str(value) if isinstance(value, Path) else value for key, value in vars(args).items()},
    }
    (args.output_dir / "run_config.json").write_text(
        json.dumps(run_config, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    training_args = TrainingArgs(
        batch_size=args.batch_size,
        iters=args.iters,
        val_batches=args.val_batches,
        steps_per_report=args.steps_per_report,
        steps_per_eval=args.steps_per_eval,
        steps_per_save=args.save_every,
        adapter_file=str(adapter_file),
        max_seq_length=args.max_seq_length,
        grad_checkpoint=args.grad_checkpoint,
    )
    optimizer = optim.AdamW(learning_rate=args.learning_rate)

    stock_evaluate = trainer_module.evaluate

    def evaluate_with_isolated_rng(*eval_args, **eval_kwargs):
        training_rng_state = np.random.get_state()
        np.random.seed(args.seed + 1_000_003)
        try:
            return stock_evaluate(*eval_args, **eval_kwargs)
        finally:
            np.random.set_state(training_rng_state)

    trainer_module.evaluate = evaluate_with_isolated_rng
    trainer_module.train(
        model=model,
        args=training_args,
        optimizer=optimizer,
        train_dataset=CacheDataset(train_set),
        val_dataset=CacheDataset(valid_set),
    )
    print(f"Final Metal peak memory: {mx.get_peak_memory() / 1e9:.3f} GB")


if __name__ == "__main__":
    main()
