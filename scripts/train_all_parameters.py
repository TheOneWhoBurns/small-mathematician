#!/usr/bin/env python3
"""Train every parameter of a local MLX-LM checkpoint.

MLX-LM's ``--fine-tune-type full --num-layers -1`` freezes the token
embedding, final normalization, and language-model head.  That is useful, but
it updates only 440.466M of Qwen3-0.6B's 596.050M parameters.  This wrapper
unfreezes the entire model so "full-model post-training" has a literal and
auditable meaning for this project.
"""

from __future__ import annotations

import argparse
import json
import platform
import time
from importlib.metadata import version
from pathlib import Path
from types import SimpleNamespace

import mlx.core as mx
import mlx.optimizers as optim
import numpy as np
import mlx_lm.tuner.trainer as trainer_module
from mlx_lm.tuner.datasets import CacheDataset, load_dataset
from mlx_lm.tuner.trainer import TrainingArgs
from mlx_lm.tuner.utils import print_trainable_parameters
from mlx_lm.utils import load


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Full-parameter MLX-LM training with no frozen modules."
    )
    parser.add_argument("--model", required=True)
    parser.add_argument(
        "--initial-weights",
        help="Optional full safetensors checkpoint to load before training.",
    )
    parser.add_argument("--data", required=True)
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--optimizer", choices=("adafactor", "adamw", "sgd"), default="adafactor")
    parser.add_argument("--batch-size", type=int, default=1)
    parser.add_argument("--iters", type=int, default=10)
    parser.add_argument("--learning-rate", type=float, default=1e-5)
    parser.add_argument("--max-seq-length", type=int, default=256)
    parser.add_argument("--grad-accumulation-steps", type=int, default=1)
    parser.add_argument("--steps-per-report", type=int, default=1)
    parser.add_argument("--steps-per-eval", type=int, default=1000)
    parser.add_argument("--val-batches", type=int, default=1)
    parser.add_argument("--save-every", type=int, default=1000)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--grad-checkpoint", action="store_true")
    parser.add_argument(
        "--mask-prompt",
        action="store_true",
        help="For prompt/completion data, compute loss on the completion only.",
    )
    parser.add_argument(
        "--raw-completions",
        action="store_true",
        help=(
            "Tokenize prompt+completion directly instead of applying the tokenizer's "
            "chat template. Requires prompt/completion JSONL and --mask-prompt."
        ),
    )
    return parser.parse_args()


class RawCompletionsDataset:
    """Prompt/completion data without chat special-token transitions."""

    def __init__(self, rows, tokenizer):
        self._data = rows
        self.tokenizer = tokenizer

    def process(self, row):
        prompt_tokens = self.tokenizer.encode(row["prompt"])
        # Generation tokenizes the complete prompt before the first completion
        # token exists, so a BPE token may not merge backward across this
        # boundary. Mirror that inference contract during training.
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
    args = parse_args()
    np.random.seed(args.seed)
    mx.random.seed(args.seed)

    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    weights_path = output_dir / "weights.safetensors"

    print("Loading pretrained model")
    model, tokenizer = load(args.model, tokenizer_config={"trust_remote_code": True})
    if args.initial_weights:
        initial_weights = Path(args.initial_weights)
        if not initial_weights.is_file():
            raise FileNotFoundError(initial_weights)
        print(f"Loading initial full weights from {initial_weights}")
        model.load_weights(str(initial_weights), strict=True)

    print("Loading datasets")
    if args.raw_completions:
        if not args.mask_prompt:
            raise ValueError("--raw-completions requires --mask-prompt")
        data_dir = Path(args.data)
        train_set = RawCompletionsDataset(load_jsonl(data_dir / "train.jsonl"), tokenizer)
        valid_set = RawCompletionsDataset(load_jsonl(data_dir / "valid.jsonl"), tokenizer)
    else:
        dataset_args = SimpleNamespace(
            data=args.data,
            train=True,
            test=False,
            mask_prompt=args.mask_prompt,
        )
        train_set, valid_set, _ = load_dataset(dataset_args, tokenizer)

    model.unfreeze()
    print("Training every model parameter")
    print_trainable_parameters(model)

    if args.optimizer == "adafactor":
        optimizer = optim.Adafactor(learning_rate=args.learning_rate)
    elif args.optimizer == "adamw":
        optimizer = optim.AdamW(learning_rate=args.learning_rate)
    else:
        optimizer = optim.SGD(learning_rate=args.learning_rate)

    training_args = TrainingArgs(
        batch_size=args.batch_size,
        iters=args.iters,
        val_batches=args.val_batches,
        steps_per_report=args.steps_per_report,
        steps_per_eval=args.steps_per_eval,
        steps_per_save=args.save_every,
        adapter_file=str(weights_path),
        max_seq_length=args.max_seq_length,
        grad_checkpoint=args.grad_checkpoint,
        grad_accumulation_steps=args.grad_accumulation_steps,
    )

    metadata = {
        "schema_version": 1,
        "created_unix": time.time(),
        "python": platform.python_version(),
        "mlx": version("mlx"),
        "mlx_lm": version("mlx-lm"),
        "device": mx.device_info(),
        "training_contract": "all model parameters unfrozen",
        "arguments": vars(args),
    }
    (output_dir / "run_config.json").write_text(
        json.dumps(metadata, indent=2, sort_keys=True) + "\n"
    )

    # MLX-LM's stock evaluate() and training iterator both consume NumPy's
    # process-global RNG.  Without isolation, changing steps_per_eval changes
    # later training batches and therefore the learned checkpoint.  Give every
    # validation call a fixed independent stream, then restore the training
    # stream exactly where it was.
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
