#!/usr/bin/env python3
"""Build verifier-oriented natural-language reasoning traces.

The inputs remain ordinary English problem statements.  The targets expose the
small arithmetic state transitions needed to reconstruct and check an answer,
instead of naming an algorithm and jumping directly to its result.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import random
from pathlib import Path

from benchmark import DATA, Instance
from build_training_data import CONCEPTS


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUTPUT = ROOT / "assets" / "data" / "processed" / "synthetic-dnl-v3-traces"
TRAIN_COUNTS = {
    "integer_expression": 250,
    "gcd_bezout": 400,
    "modular_inverse": 600,
    "quadratic_integer_roots": 600,
    "linear_system": 650,
}
EVAL_COUNTS = {family: 40 for family in TRAIN_COUNTS}


def extended_gcd_trace(a: int, b: int) -> tuple[int, int, int, list[tuple[int, int, int, int]]]:
    old_r, r, old_s, s, old_t, t = a, b, 1, 0, 0, 1
    divisions: list[tuple[int, int, int, int]] = []
    while r:
        quotient = old_r // r
        next_r = old_r - quotient * r
        divisions.append((old_r, quotient, r, next_r))
        old_r, r = r, next_r
        old_s, s = s, old_s - quotient * s
        old_t, t = t, old_t - quotient * t
    return old_r, old_s, old_t, divisions


def division_trace(divisions: list[tuple[int, int, int, int]]) -> str:
    return " ".join(
        f"Divide {dividend} by {divisor}: {dividend} equals {quotient} times {divisor} plus {remainder}."
        for dividend, quotient, divisor, remainder in divisions
    )


def signed(value: int, noun: str = "") -> str:
    words = f"{abs(value)}{(' ' + noun) if noun else ''}"
    return f"plus {words}" if value >= 0 else f"minus {words}"


def equation(cx: int, cy: int, rhs: int) -> str:
    joiner = "plus" if cy >= 0 else "minus"
    return f"{cx} times x {joiner} {abs(cy)} times y equals {rhs}"


def factor(root: int) -> str:
    return f"x minus {root}" if root >= 0 else f"x plus {abs(root)}"


def coprime_pair(rng: random.Random, low: int, high: int) -> tuple[int, int]:
    while True:
        first, second = rng.randint(low, high), rng.randint(low, high)
        if first != second and math.gcd(first, second) == 1:
            return first, second


def make_instance(rng: random.Random, family: str) -> Instance:
    if family == "integer_expression":
        a, b, c, d = (rng.randint(2, 100) for _ in range(4))
        answer = (a + b) * c - d
        prompt = (
            f"Evaluate the quantity {a} plus {b}, multiplied by {c}, and then reduced by {d}. "
            "Explain your calculation briefly. End with a sentence of the form 'The answer is N.'"
        )
        verifier = {"answer": answer, "operands": [a, b, c, d]}
    elif family == "gcd_bezout":
        p, q = coprime_pair(rng, 3, 70)
        scale = rng.randint(2, 20)
        a, b = scale * p, scale * q
        g, x, y, _trace = extended_gcd_trace(a, b)
        prompt = (
            f"Find the greatest common divisor of {a} and {b}. Also give integer coefficients x and y "
            f"that certify the result by making {a} times x plus {b} times y equal to the greatest "
            "common divisor. Explain your reasoning briefly. End with: 'The greatest common divisor "
            "is G; coefficients x = X and y = Y certify it.'"
        )
        verifier = {"a": a, "b": b, "gcd": g, "canonical_x": x, "canonical_y": y}
    elif family == "modular_inverse":
        modulus = rng.randint(11, 300)
        value = rng.randint(2, modulus - 1)
        while math.gcd(value, modulus) != 1:
            value = rng.randint(2, modulus - 1)
        g, coefficient, _other, _trace = extended_gcd_trace(value, modulus)
        assert g == 1
        inverse = coefficient % modulus
        prompt = (
            f"Find the least nonnegative multiplicative inverse of {value} modulo {modulus}. In other "
            f"words, find the least nonnegative integer which, when multiplied by {value}, leaves "
            f"remainder 1 after division by {modulus}. Explain your reasoning briefly. End with a "
            "sentence of the form 'The inverse is I.'"
        )
        verifier = {"value": value, "modulus": modulus, "inverse": inverse}
    elif family == "quadratic_integer_roots":
        choices = [number for number in range(-25, 26) if number]
        first, second = rng.sample(choices, 2)
        linear, constant = -(first + second), first * second
        prompt = (
            f"Find both integer roots of the equation x squared {signed(linear, 'times x')} "
            f"{signed(constant)} equals zero. Explain how you know both roots are correct. "
            "End with: 'The integer roots are R and S.'"
        )
        verifier = {"linear": linear, "constant": constant, "roots": sorted((first, second))}
    elif family == "linear_system":
        choices = [number for number in range(-8, 9) if number]
        while True:
            a, b, c, d = (rng.choice(choices) for _ in range(4))
            if a * d - b * c:
                break
        x, y = rng.randint(-12, 12), rng.randint(-12, 12)
        rhs1, rhs2 = a * x + b * y, c * x + d * y
        prompt = (
            f"Find the unique integer solution x and y to these two equations: {equation(a, b, rhs1)}; "
            f"and {equation(c, d, rhs2)}. Explain your reasoning briefly. End with: "
            "'The solution is x = X and y = Y.'"
        )
        verifier = {"a": a, "b": b, "c": c, "d": d, "rhs1": rhs1, "rhs2": rhs2, "x": x, "y": y}
    else:
        raise ValueError(family)

    digest = hashlib.sha256(prompt.encode()).hexdigest()[:12]
    return Instance(
        id=f"dnl-train-v3-{family}-{digest}",
        split="synthetic",
        family=family,
        prompt=prompt,
        verifier=verifier,
    )


def trace_solution(instance: Instance) -> str:
    family, value = instance.family, instance.verifier
    if family == "integer_expression":
        a, b, c, d = value["operands"]
        subtotal, product = a + b, (a + b) * c
        body = (
            f"Add {a} and {b} to get {subtotal}. Multiply {subtotal} by {c} to get {product}. "
            f"Subtract {d} from {product} to get {value['answer']}. The answer is {value['answer']}."
        )
    elif family == "gcd_bezout":
        a, b = value["a"], value["b"]
        g, x, y, divisions = extended_gcd_trace(a, b)
        body = (
            f"{division_trace(divisions)} The last nonzero remainder is {g}, so it is the greatest "
            f"common divisor. Tracking the remainders back gives {g} equals {a} times {x} plus {b} "
            f"times {y}. Checking the certificate, {a * x} plus {b * y} equals {g}. "
            f"The greatest common divisor is {g}; coefficients x = {x} and y = {y} certify it."
        )
    elif family == "modular_inverse":
        number, modulus = value["value"], value["modulus"]
        g, coefficient, other, divisions = extended_gcd_trace(number, modulus)
        assert g == 1
        inverse = coefficient % modulus
        quotient = (number * inverse - 1) // modulus
        body = (
            f"{division_trace(divisions)} Tracking the remainders back gives 1 equals {number} times "
            f"{coefficient} plus {modulus} times {other}. Reduce the coefficient {coefficient} to the "
            f"least nonnegative residue {inverse}. Check: {number} times {inverse} equals "
            f"{number * inverse}, which is 1 plus {quotient} times {modulus}. The inverse is {inverse}."
        )
    elif family == "quadratic_integer_roots":
        first, second = value["roots"]
        linear, constant = value["linear"], value["constant"]
        first_check = first * first + linear * first + constant
        second_check = second * second + linear * second + constant
        body = (
            f"The numbers {first} and {second} add to {-linear} and multiply to {constant}. Therefore "
            f"the quadratic factors as ({factor(first)}) times ({factor(second)}). Each factor can be "
            f"zero. Substituting {first} in the original expression gives {first_check}; substituting "
            f"{second} gives {second_check}. The integer roots are {first} and {second}."
        )
    elif family == "linear_system":
        a, b, c, d = value["a"], value["b"], value["c"], value["d"]
        rhs1, rhs2, x, y = value["rhs1"], value["rhs2"], value["x"], value["y"]
        determinant = a * d - b * c
        x_numerator = rhs1 * d - b * rhs2
        y_numerator = a * rhs2 - rhs1 * c
        body = (
            f"The determinant is {a} times {d} minus {b} times {c}, which equals {determinant}. "
            f"It is nonzero, so the solution is unique. The numerator for x is {rhs1} times {d} "
            f"minus {b} times {rhs2}, which equals {x_numerator}; dividing by {determinant} gives x "
            f"equals {x}. The numerator for y is {a} times {rhs2} minus {rhs1} times {c}, which "
            f"equals {y_numerator}; dividing by {determinant} gives y equals {y}. Checking gives "
            f"{a * x + b * y} in the first equation and {c * x + d * y} in the second. "
            f"The solution is x = {x} and y = {y}."
        )
    else:
        raise ValueError(family)
    return f"Relevant ideas: {CONCEPTS[family]}\nReasoning: {body}"


def frozen_prompts() -> set[str]:
    return {
        json.loads(line)["prompt"]
        for split in ("dev", "test")
        for line in (DATA / f"{split}.prompts.jsonl").read_text().splitlines()
        if line.strip()
    }


def build_split(seed: int, counts: dict[str, int], forbidden: set[str]) -> tuple[list[dict], set[str]]:
    rng = random.Random(seed)
    rows: list[dict] = []
    produced: set[str] = set()
    for family, count in counts.items():
        family_rows = 0
        while family_rows < count:
            instance = make_instance(rng, family)
            if instance.prompt in forbidden or instance.prompt in produced:
                continue
            rows.append(
                {
                    "prompt": "Respond only in English.\nProblem: " + instance.prompt,
                    "completion": trace_solution(instance),
                    "metadata": {
                        "source": "deterministic-nl-synthetic-v3-traces",
                        "family": family,
                        "synthetic_id": instance.id,
                    },
                }
            )
            produced.add(instance.prompt)
            family_rows += 1
    rng.shuffle(rows)
    return rows, produced


def payload_hash(rows: list[dict]) -> str:
    payload = "".join(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n" for row in rows)
    return hashlib.sha256(payload.encode()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()

    forbidden = frozen_prompts()
    specs = {
        "train": (20260810, TRAIN_COUNTS),
        "valid": (20260811, EVAL_COUNTS),
        "test": (20260812, EVAL_COUNTS),
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
        "schema_version": 3,
        "purpose": "natural-language arithmetic state traces for verifier-oriented reasoning",
        "formal_data_read": False,
        "chat_template_used": False,
        "counts": {split: len(rows) for split, rows in all_rows.items()},
        "family_counts": {"train": TRAIN_COUNTS, "valid": EVAL_COUNTS, "test": EVAL_COUNTS},
        "seeds": {split: seed for split, (seed, _counts) in specs.items()},
        "sha256": {split: payload_hash(rows) for split, rows in all_rows.items()},
        "frozen_benchmark_prompts_excluded": 200,
    }
    (args.output / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
