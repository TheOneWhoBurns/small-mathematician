#!/usr/bin/env python3
"""Build direct coefficient-state and elimination supervision.

This is a deliberately small follow-up curriculum.  It replaces verbal jumps
such as "back-substitution gives" with the exact natural-language state updates
that produce each coefficient or eliminated equation.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import random
from pathlib import Path

from build_trace_training_data import (
    DEFAULT_OUTPUT as _UNUSED_DEFAULT,
    extended_gcd_trace,
    factor,
    frozen_prompts,
    make_instance,
    payload_hash,
)


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUTPUT = ROOT / "assets" / "data" / "processed" / "synthetic-dnl-v4-states"
TRAIN_COUNTS = {
    "integer_expression": 300,
    "gcd_bezout": 250,
    "modular_inverse": 250,
    "quadratic_integer_roots": 100,
    "linear_system": 300,
}
EVAL_COUNTS = {family: 40 for family in TRAIN_COUNTS}


def coefficient_states(a: int, b: int) -> tuple[int, int, int, list[tuple[int, int, int, int]]]:
    old_r, r, old_s, s, old_t, t = a, b, 1, 0, 0, 1
    states: list[tuple[int, int, int, int]] = []
    while r:
        quotient = old_r // r
        next_r = old_r - quotient * r
        next_s = old_s - quotient * s
        next_t = old_t - quotient * t
        assert next_r == a * next_s + b * next_t
        states.append((quotient, next_r, next_s, next_t))
        old_r, r = r, next_r
        old_s, s = s, next_s
        old_t, t = t, next_t
    assert old_r == a * old_s + b * old_t
    return old_r, old_s, old_t, states


def state_sentences(a: int, b: int, states: list[tuple[int, int, int, int]]) -> str:
    pieces = [
        f"Start with {a} having coefficients 1 and 0, and {b} having coefficients 0 and 1."
    ]
    for quotient, remainder, first_coefficient, second_coefficient in states:
        if remainder == 0:
            pieces.append(f"The next quotient is {quotient}, producing remainder 0, so stop.")
        else:
            pieces.append(
                f"With quotient {quotient}, the next remainder is {remainder}; its coefficients are "
                f"{first_coefficient} and {second_coefficient}, because {a} times {first_coefficient} "
                f"plus {b} times {second_coefficient} equals {remainder}."
            )
    return " ".join(pieces)


def direct_solution(instance) -> str:
    family, value = instance.family, instance.verifier
    if family == "integer_expression":
        a, b, c, d = value["operands"]
        subtotal, product, answer = a + b, (a + b) * c, value["answer"]
        return (
            "Relevant ideas: arithmetic order; checking\n"
            f"Reasoning: Add {a} and {b} to get {subtotal}. Multiply {subtotal} by {c} to get "
            f"{product}. Subtract {d} to get {answer}. Check: {subtotal} times {c} minus {d} "
            f"equals {answer}. The answer is {answer}."
        )

    if family == "gcd_bezout":
        a, b = value["a"], value["b"]
        gcd_value, x, y, states = coefficient_states(a, b)
        assert gcd_value == value["gcd"] and a * x + b * y == gcd_value
        return (
            "Relevant ideas: Euclidean algorithm; coefficient tracking\n"
            f"Reasoning: {state_sentences(a, b, states)} The last nonzero remainder is {gcd_value}. "
            f"Certificate: {a} times {x} plus {b} times {y} equals {gcd_value}. "
            f"The greatest common divisor is {gcd_value}; coefficients x = {x} and y = {y} certify it."
        )

    if family == "modular_inverse":
        number, modulus = value["value"], value["modulus"]
        gcd_value, coefficient, other, states = coefficient_states(number, modulus)
        assert gcd_value == 1
        inverse = coefficient % modulus
        quotient = (number * inverse - 1) // modulus
        assert number * inverse == 1 + quotient * modulus
        return (
            "Relevant ideas: coefficient tracking; modular check\n"
            f"Reasoning: {state_sentences(number, modulus, states)} Thus 1 equals {number} times "
            f"{coefficient} plus {modulus} times {other}. Reduce {coefficient} to the least "
            f"nonnegative residue {inverse}. Certificate: {number} times {inverse} equals "
            f"{number * inverse}, and 1 plus {quotient} times {modulus} also equals "
            f"{number * inverse}. The inverse is {inverse}."
        )

    if family == "quadratic_integer_roots":
        first, second = value["roots"]
        linear, constant = value["linear"], value["constant"]
        assert first + second == -linear and first * second == constant
        assert first * first + linear * first + constant == 0
        assert second * second + linear * second + constant == 0
        return (
            "Relevant ideas: factorization; substitution\n"
            f"Reasoning: The roots must add to {-linear} and multiply to {constant}. The numbers "
            f"{first} and {second} do both, so the factorization is ({factor(first)}) times "
            f"({factor(second)}). Check: substituting {first} gives 0, and substituting {second} "
            f"gives 0. The integer roots are {first} and {second}."
        )

    if family == "linear_system":
        a, b, c, d = value["a"], value["b"], value["c"], value["d"]
        first_rhs, second_rhs = value["rhs1"], value["rhs2"]
        x, y = value["x"], value["y"]
        determinant = a * d - b * c
        x_numerator = first_rhs * d - second_rhs * b
        y_numerator = a * second_rhs - c * first_rhs
        assert determinant and x_numerator == determinant * x and y_numerator == determinant * y
        assert a * x + b * y == first_rhs and c * x + d * y == second_rhs
        return (
            "Relevant ideas: elimination; checking\n"
            f"Reasoning: To remove y, multiply the first equation by {d} and the second equation by "
            f"{b}. Both y terms then have coefficient {b * d}. Subtract the second scaled equation "
            f"from the first: {determinant} times x equals {x_numerator}, so x equals {x}. To remove "
            f"x, multiply the second equation by {a} and the first equation by {c}. Both x terms then "
            f"have coefficient {a * c}. Subtract the first scaled equation from the second: "
            f"{determinant} times y equals {y_numerator}, so y equals {y}. Check: the first left side "
            f"is {a * x + b * y}, and the second left side is {c * x + d * y}. "
            f"The solution is x = {x} and y = {y}."
        )

    raise ValueError(family)


def prior_training_prompts() -> set[str]:
    prompts: set[str] = set()
    for directory in (
        ROOT / "assets/data/processed/synthetic-dnl-v2-expanded",
        ROOT / "assets/data/processed/synthetic-dnl-v3-traces",
    ):
        for split in ("train", "valid", "test"):
            path = directory / f"{split}.jsonl"
            if not path.exists():
                continue
            for line in path.read_text().splitlines():
                if not line.strip():
                    continue
                prompt = json.loads(line)["prompt"]
                prompts.add(prompt.removeprefix("Respond only in English.\nProblem: "))
    return prompts


def build_split(seed: int, counts: dict[str, int], forbidden: set[str]) -> tuple[list[dict], set[str]]:
    rng = random.Random(seed)
    rows: list[dict] = []
    produced: set[str] = set()
    for family, count in counts.items():
        accepted = 0
        while accepted < count:
            instance = make_instance(rng, family)
            if instance.prompt in forbidden or instance.prompt in produced:
                continue
            if family in ("gcd_bezout", "modular_inverse"):
                a = instance.verifier.get("a", instance.verifier.get("value"))
                b = instance.verifier.get("b", instance.verifier.get("modulus"))
                _g, _x, _y, divisions = extended_gcd_trace(a, b)
                if not 2 <= len(divisions) <= 7:
                    continue
            completion = direct_solution(instance)
            if len(completion.split()) > 220:
                continue
            rows.append(
                {
                    "prompt": "Respond only in English.\nProblem: " + instance.prompt,
                    "completion": completion,
                    "metadata": {
                        "source": "deterministic-nl-synthetic-v4-states",
                        "family": family,
                        "synthetic_id": instance.id,
                    },
                }
            )
            produced.add(instance.prompt)
            accepted += 1
    rng.shuffle(rows)
    return rows, produced


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()

    forbidden = frozen_prompts() | prior_training_prompts()
    specs = {
        "train": (20260820, TRAIN_COUNTS),
        "valid": (20260821, EVAL_COUNTS),
        "test": (20260822, EVAL_COUNTS),
    }
    all_rows: dict[str, list[dict]] = {}
    for split, (seed, counts) in specs.items():
        rows, produced = build_split(seed, counts, forbidden)
        all_rows[split] = rows
        forbidden.update(produced)

    args.output.mkdir(parents=True, exist_ok=True)
    for split, rows in all_rows.items():
        with (args.output / f"{split}.jsonl").open("w", encoding="utf-8") as handle:
            for row in rows:
                handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")

    manifest = {
        "schema_version": 4,
        "purpose": "direct coefficient-state and equation-elimination natural-language supervision",
        "formal_data_read": False,
        "counts": {split: len(rows) for split, rows in all_rows.items()},
        "family_counts": {"train": TRAIN_COUNTS, "valid": EVAL_COUNTS, "test": EVAL_COUNTS},
        "seeds": {split: seed for split, (seed, _counts) in specs.items()},
        "sha256": {split: payload_hash(rows) for split, rows in all_rows.items()},
        "exact_prior_and_benchmark_prompts_excluded": len(frozen_prompts() | prior_training_prompts()),
        "target_word_limit": 220,
        "euclid_division_depth": [2, 7],
    }
    (args.output / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
