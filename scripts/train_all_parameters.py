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
import re
import time
from importlib.metadata import version
from pathlib import Path
from types import SimpleNamespace

import mlx.core as mx
import mlx.nn as nn
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
    parser.add_argument(
        "--digit-token-loss",
        action="store_true",
        help="With raw completions, compute loss only on decimal digit tokens in the completion.",
    )
    parser.add_argument(
        "--first-step-loss",
        action="store_true",
        help="With raw completions, compute loss only through the first Euclidean-step sentence.",
    )
    parser.add_argument(
        "--second-step-loss",
        action="store_true",
        help="With raw completions, compute loss only on the second Euclidean-step sentence.",
    )
    parser.add_argument(
        "--first-two-step-loss",
        action="store_true",
        help="With raw completions, compute loss on the first two Euclidean-step sentences together.",
    )
    return parser.parse_args()


class RawCompletionsDataset:
    """Prompt/completion data without chat special-token transitions."""

    def __init__(self, rows, tokenizer, loss_mode="full"):
        self._data = rows
        self.tokenizer = tokenizer
        self.loss_mode = loss_mode
        self.digit_token_ids = {
            tokenizer.encode(str(digit), add_special_tokens=False)[0] for digit in range(10)
        }

    def process(self, row):
        prompt_tokens = self.tokenizer.encode(row["prompt"])
        # Generation tokenizes the complete prompt before the first completion
        # token exists, so a BPE token may not merge backward across this
        # boundary. Mirror that inference contract during training.
        completion_tokens = self.tokenizer.encode(row["completion"])
        tokens = prompt_tokens + completion_tokens
        if tokens[-1] != self.tokenizer.eos_token_id:
            tokens.append(self.tokenizer.eos_token_id)
        if self.loss_mode == "digits":
            token_mask = [0] * len(prompt_tokens) + [int(token in self.digit_token_ids) for token in completion_tokens]
            if len(token_mask) < len(tokens):
                token_mask.append(0)
            return tokens, token_mask
        if self.loss_mode == "first_step":
            marker = "."
            first_end = row["completion"].find(marker)
            if first_end < 0 or not row["completion"].startswith("Euclidean step:"):
                raise ValueError("--first-step-loss requires completions beginning with a Euclidean step sentence")
            first_sentence = row["completion"][: first_end + len(marker)]
            first_tokens = self.tokenizer.encode(first_sentence)
            if completion_tokens[: len(first_tokens)] != first_tokens:
                raise ValueError("first-step tokenization is not a prefix of full-completion tokenization")
            token_mask = [0] * len(prompt_tokens) + [1] * len(first_tokens) + [0] * (len(completion_tokens) - len(first_tokens))
            if len(token_mask) < len(tokens):
                token_mask.append(0)
            return tokens, token_mask
        if self.loss_mode == "second_step":
            starts = [match.start() for match in re.finditer("Euclidean step:", row["completion"])]
            if len(starts) < 2:
                raise ValueError("--second-step-loss requires at least two Euclidean step sentences")
            second_start = starts[1]
            second_end = row["completion"].find(".", second_start)
            if second_end < 0:
                raise ValueError("second Euclidean step has no sentence terminator")
            def first_prefix_reaching(char_offset: int) -> int:
                low, high = 0, len(completion_tokens)
                while low < high:
                    middle = (low + high) // 2
                    if len(self.tokenizer.decode(completion_tokens[:middle])) >= char_offset:
                        high = middle
                    else:
                        low = middle + 1
                return low

            # Include a token if any of its decoded characters overlap the
            # target sentence; this handles BPE pieces such as ``". Eu"``.
            first_end_token = first_prefix_reaching(second_start + 1)
            target_start = max(0, first_end_token - 1)
            target_end = first_prefix_reaching(second_end + 1)
            token_mask = [0] * len(prompt_tokens) + [0] * target_start + [1] * (target_end - target_start) + [0] * (len(completion_tokens) - target_end)
            if len(token_mask) < len(tokens):
                token_mask.append(0)
            return tokens, token_mask
        if self.loss_mode == "first_two_steps":
            starts = [match.start() for match in re.finditer("Euclidean step:", row["completion"])]
            if len(starts) < 2:
                raise ValueError("--first-two-step-loss requires at least two Euclidean step sentences")
            second_end = row["completion"].find(".", starts[1])
            if second_end < 0:
                raise ValueError("second Euclidean step has no sentence terminator")

            low, high = 0, len(completion_tokens)
            while low < high:
                middle = (low + high) // 2
                if len(self.tokenizer.decode(completion_tokens[:middle])) >= second_end + 1:
                    high = middle
                else:
                    low = middle + 1
            target_end = low
            token_mask = [0] * len(prompt_tokens) + [1] * target_end + [0] * (len(completion_tokens) - target_end)
            if len(token_mask) < len(tokens):
                token_mask.append(0)
            return tokens, token_mask
        return tokens, len(prompt_tokens)

    def __getitem__(self, index):
        return self._data[index]

    def __len__(self):
        return len(self._data)


def load_jsonl(path: Path):
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def masked_token_loss(model, batch, token_mask):
    inputs = batch[:, :-1]
    targets = batch[:, 1:]
    mask = token_mask[:, 1:]
    logits = model(inputs)
    ce = nn.losses.cross_entropy(logits, targets) * mask
    ntoks = mask.sum()
    return ce.astype(mx.float32).sum() / ntoks, ntoks


def masked_token_batches(dataset, batch_size, max_seq_length, loop=False, seed=None, comm_group=None):
    if comm_group is not None and comm_group.size() != 1:
        raise ValueError("focused token loss currently supports one local worker")
    indices = list(range(len(dataset)))
    if len(indices) < batch_size:
        raise ValueError("dataset smaller than batch size")
    batches = [indices[start : start + batch_size] for start in range(0, len(indices) - batch_size + 1, batch_size)]
    if seed is not None:
        np.random.seed(seed)
    while True:
        for batch_index in np.random.permutation(len(batches)):
            examples = [dataset[index] for index in batches[batch_index]]
            tokens, masks = zip(*examples)
            lengths = [min(len(value), max_seq_length) for value in tokens]
            padded_length = min(1 + 32 * ((max(lengths) + 31) // 32), max_seq_length)
            batch_array = np.zeros((batch_size, padded_length), dtype=np.int32)
            mask_array = np.zeros((batch_size, padded_length), dtype=np.float32)
            for row_index, (token_row, mask_row) in enumerate(zip(tokens, masks)):
                length = min(len(token_row), padded_length)
                batch_array[row_index, :length] = token_row[:length]
                mask_array[row_index, :length] = mask_row[:length]
            yield mx.array(batch_array), mx.array(mask_array)
        if not loop:
            break


def main() -> None:
    args = parse_args()
    focused_modes = sum((args.digit_token_loss, args.first_step_loss, args.second_step_loss, args.first_two_step_loss))
    if focused_modes > 1:
        raise ValueError("choose at most one focused-loss mode")
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
        loss_mode = "digits" if args.digit_token_loss else "first_step" if args.first_step_loss else "second_step" if args.second_step_loss else "first_two_steps" if args.first_two_step_loss else "full"
        train_rows = load_jsonl(data_dir / "train.jsonl")
        valid_rows = load_jsonl(data_dir / "valid.jsonl")
        if loss_mode in {"second_step", "first_two_steps"}:
            train_rows = [row for row in train_rows if row["completion"].count("Euclidean step:") >= 2]
            valid_rows = [row for row in valid_rows if row["completion"].count("Euclidean step:") >= 2]
            print(f"Two-step eligible rows: train={len(train_rows)}, valid={len(valid_rows)}")
        train_set = RawCompletionsDataset(train_rows, tokenizer, loss_mode)
        valid_set = RawCompletionsDataset(valid_rows, tokenizer, loss_mode)
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
        loss=masked_token_loss if focused_modes else trainer_module.default_loss,
        iterate_batches=masked_token_batches if focused_modes else trainer_module.iterate_batches,
    )
    print(f"Final Metal peak memory: {mx.get_peak_memory() / 1e9:.3f} GB")


if __name__ == "__main__":
    main()
