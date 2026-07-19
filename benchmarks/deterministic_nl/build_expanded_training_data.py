#!/usr/bin/env python3
"""Build broad, English-only algorithmic supervision disjoint from benchmark prompts."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import random
from pathlib import Path

from benchmark import DATA, Instance
from build_training_data import CONCEPTS, solution


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUTPUT = ROOT / "assets" / "data" / "processed" / "synthetic-dnl-v2-expanded"
FAMILIES = tuple(CONCEPTS)


def extended_gcd(a: int, b: int) -> tuple[int, int, int]:
    old_r, r, old_s, s, old_t, t = a, b, 1, 0, 0, 1
    while r:
        quotient = old_r // r
        old_r, r = r, old_r - quotient * r
        old_s, s = s, old_s - quotient * s
        old_t, t = t, old_t - quotient * t
    return old_r, old_s, old_t


def signed(value: int, noun: str) -> str:
    return f"plus {value} {noun}" if value >= 0 else f"minus {abs(value)} {noun}"


def make_problem(rng: random.Random, family: str) -> tuple[str, dict]:
    if family == "integer_expression":
        a, b, c, d = (rng.randint(2, 180) for _ in range(4))
        answer = (a + b) * c - d
        prompt = (
            f"Evaluate the quantity {a} plus {b}, multiplied by {c}, and then reduced by {d}. "
            "Explain your calculation briefly. End with a sentence of the form 'The answer is N.'"
        )
        verifier = {"answer": answer, "operands": [a, b, c, d]}
    elif family == "gcd_bezout":
        a, b = rng.sample(range(12, 1200), 2)
        g, x, y = extended_gcd(a, b)
        prompt = (
            f"Find the greatest common divisor of {a} and {b}. Also give integer coefficients x and y "
            f"that certify the result by making {a} times x plus {b} times y equal to the greatest "
            "common divisor. Explain your reasoning briefly. End with: 'The greatest common divisor "
            "is G; coefficients x = X and y = Y certify it.'"
        )
        verifier = {"a": a, "b": b, "gcd": g, "canonical_x": x, "canonical_y": y}
    elif family == "modular_inverse":
        modulus = rng.randint(11, 1200)
        value = rng.randint(2, modulus - 1)
        while math.gcd(value, modulus) != 1:
            value = rng.randint(2, modulus - 1)
        inverse = pow(value, -1, modulus)
        prompt = (
            f"Find the least nonnegative multiplicative inverse of {value} modulo {modulus}. In other "
            f"words, find the least nonnegative integer which, when multiplied by {value}, leaves "
            f"remainder 1 after division by {modulus}. Explain your reasoning briefly. End with a "
            "sentence of the form 'The inverse is I.'"
        )
        verifier = {"value": value, "modulus": modulus, "inverse": inverse}
    elif family == "quadratic_integer_roots":
        roots = [number for number in range(-80, 81) if number]
        first, second = rng.sample(roots, 2)
        linear, constant = -(first + second), first * second
        prompt = (
            f"Find both integer roots of the equation x squared {signed(linear, 'times x')} "
            f"{signed(constant, '')} equals zero. Explain how you know both roots are correct. "
            "End with: 'The integer roots are R and S.'"
        ).replace("  ", " ")
        verifier = {"linear": linear, "constant": constant, "roots": sorted((first, second))}
    elif family == "linear_system":
        while True:
            a, b, c, d = (rng.choice([n for n in range(-25, 26) if n]) for _ in range(4))
            if a * d - b * c:
                break
        x, y = rng.randint(-80, 80), rng.randint(-80, 80)
        rhs1, rhs2 = a * x + b * y, c * x + d * y
        def equation(cx: int, cy: int, rhs: int) -> str:
            joiner = "plus" if cy >= 0 else "minus"
            return f"{cx} times x {joiner} {abs(cy)} times y equals {rhs}"
        prompt = (
            f"Find the unique integer solution x and y to these two equations: {equation(a, b, rhs1)}; "
            f"and {equation(c, d, rhs2)}. Explain your reasoning briefly. End with: "
            "'The solution is x = X and y = Y.'"
        )
        verifier = {"a": a, "b": b, "c": c, "d": d, "rhs1": rhs1, "rhs2": rhs2, "x": x, "y": y}
    else:
        raise ValueError(family)
    return prompt, verifier


def frozen_prompts() -> set[str]:
    return {
        json.loads(line)["prompt"]
        for split in ("dev", "test")
        for line in (DATA / f"{split}.prompts.jsonl").read_text().splitlines()
        if line.strip()
    }


def build_split(seed: int, per_family: int, forbidden: set[str]) -> tuple[list[dict], set[str]]:
    rng = random.Random(seed)
    rows: list[dict] = []
    produced: set[str] = set()
    for family in FAMILIES:
        family_rows = 0
        while family_rows < per_family:
            prompt, verifier = make_problem(rng, family)
            if prompt in forbidden or prompt in produced:
                continue
            digest = hashlib.sha256(prompt.encode()).hexdigest()[:12]
            instance = Instance(
                id=f"dnl-train-v2-{family}-{digest}",
                split="synthetic",
                family=family,
                prompt=prompt,
                verifier=verifier,
            )
            rows.append(
                {
                    "prompt": "Respond only in English.\nProblem: " + prompt,
                    "completion": solution(instance),
                    "metadata": {
                        "source": "deterministic-nl-synthetic-v2-expanded",
                        "family": family,
                        "synthetic_id": instance.id,
                    },
                }
            )
            produced.add(prompt)
            family_rows += 1
    rng.shuffle(rows)
    return rows, produced


def payload_hash(rows: list[dict]) -> str:
    payload = "".join(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n" for row in rows)
    return hashlib.sha256(payload.encode()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--train-per-family", type=int, default=500)
    parser.add_argument("--valid-per-family", type=int, default=50)
    parser.add_argument("--test-per-family", type=int, default=50)
    args = parser.parse_args()

    forbidden = frozen_prompts()
    specs = {
        "train": (20260730, args.train_per_family),
        "valid": (20260731, args.valid_per_family),
        "test": (20260801, args.test_per_family),
    }
    all_rows = {}
    for split, (seed, per_family) in specs.items():
        rows, produced = build_split(seed, per_family, forbidden)
        all_rows[split] = rows
        forbidden.update(produced)

    args.output.mkdir(parents=True, exist_ok=True)
    for split, rows in all_rows.items():
        with (args.output / f"{split}.jsonl").open("w", encoding="utf-8") as handle:
            for row in rows:
                handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
    manifest = {
        "schema_version": 2,
        "purpose": "broad English-only algorithmic supervision disjoint from all frozen benchmark prompts",
        "formal_data_read": False,
        "chat_user_prefix": "Respond only in English.\\nProblem: ",
        "answer_cue_inside_user_message": False,
        "families": list(FAMILIES),
        "seeds": {split: seed for split, (seed, _count) in specs.items()},
        "counts": {split: len(rows) for split, rows in all_rows.items()},
        "sha256": {split: payload_hash(rows) for split, rows in all_rows.items()},
    }
    (args.output / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
