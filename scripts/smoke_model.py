#!/usr/bin/env python3
"""Load the local 0.6B base model through MLX and generate a few tokens."""

from pathlib import Path

from mlx_lm import generate, load


ROOT = Path(__file__).resolve().parents[1]
MODEL_PATH = ROOT / "assets" / "models" / "qwen3-0.6b-base"


def main() -> None:
    model, tokenizer = load(str(MODEL_PATH))
    prompt = "Problem: Prove that the sum of two even integers is even.\nIdea:"
    response = generate(model, tokenizer, prompt=prompt, max_tokens=12, verbose=False)
    print(response)


if __name__ == "__main__":
    main()

