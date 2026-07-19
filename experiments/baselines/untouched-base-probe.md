# Untouched Base Qualitative Probe

Model: `Qwen/Qwen3-0.6B-Base`, pinned local BF16 checkpoint.

Generation: raw prompt, greedy decoding, 120-token limit. These prompts are not
from the sealed evaluations and this is not a scored benchmark.

## Modular arithmetic

Prompt: Find the remainder when `7^13` is divided by `10` and justify it.

Observed result: The model answered `3`, correctly, and appealed to the last
digit, but began repeating the problem before the token limit.

## Divisibility proof

Prompt: Prove that the product of three consecutive integers is divisible by
`6`; give a concise proof blueprint.

Observed result: The model restated the theorem and then emitted only `6`. It did
not supply the parity/modulo-3 argument.

## Linear equation

Prompt: Solve `7x + 5 = 47` and justify the answer.

Observed result: It correctly isolated `x` step by step and concluded `x = 6`.

## Interpretation

The untouched model already has some elementary answer competence. Early
experiments therefore need to test proof construction and retention, not merely
whether supervised training can teach a few arithmetic outputs.

