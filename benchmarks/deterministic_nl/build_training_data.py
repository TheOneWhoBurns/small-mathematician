#!/usr/bin/env python3
"""Generate disjoint natural-language supervision for benchmark families."""

from __future__ import annotations

import argparse
import hashlib
import json
import random
from pathlib import Path

from benchmark import DATA, Instance, generate_instances


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUTPUT = ROOT / "assets" / "data" / "processed" / "synthetic-dnl-v1"

CONCEPTS = {
    "integer_expression": "arithmetic order; substitution; checking",
    "gcd_bezout": "Euclidean algorithm; divisibility; Bezout certificate",
    "modular_inverse": "modular arithmetic; multiplicative inverse; certificate",
    "quadratic_integer_roots": "factorization; roots; substitution check",
    "linear_system": "elimination; determinant; substitution check",
}


def solution(instance: Instance) -> str:
    value = instance.verifier
    family = instance.family
    if family == "integer_expression":
        a, b, c, d = value["operands"]
        subtotal = a + b
        product = subtotal * c
        body = (
            f"Add {a} and {b} to get {subtotal}. Multiplying by {c} gives {product}. "
            f"Subtracting {d} gives {value['answer']}. The answer is {value['answer']}."
        )
    elif family == "gcd_bezout":
        a, b, g = value["a"], value["b"], value["gcd"]
        x, y = value["canonical_x"], value["canonical_y"]
        body = (
            f"The Euclidean algorithm gives greatest common divisor {g}. A direct certificate is "
            f"{a} times {x} plus {b} times {y}, which equals {a*x+b*y}. "
            f"The greatest common divisor is {g}; coefficients x = {x} and y = {y} certify it."
        )
    elif family == "modular_inverse":
        number, modulus, inverse = value["value"], value["modulus"], value["inverse"]
        product = number * inverse
        quotient = (product - 1) // modulus
        body = (
            f"Multiplying {number} by {inverse} gives {product}, and {product} equals 1 plus "
            f"{quotient} times {modulus}. Thus the product leaves remainder 1 modulo {modulus}; "
            f"{inverse} is already in the required range. The inverse is {inverse}."
        )
    elif family == "quadratic_integer_roots":
        first, second = value["roots"]
        linear, constant = value["linear"], value["constant"]
        body = (
            f"The two numbers {first} and {second} add to {-linear} and multiply to {constant}. "
            f"Therefore the polynomial factors as (x minus {first}) times (x minus {second}). "
            f"Each factor can be zero, and substitution checks both values. "
            f"The integer roots are {first} and {second}."
        )
    elif family == "linear_system":
        a, b, c, d = value["a"], value["b"], value["c"], value["d"]
        rhs1, rhs2 = value["rhs1"], value["rhs2"]
        x, y = value["x"], value["y"]
        determinant = a * d - b * c
        body = (
            f"Elimination uses the nonzero determinant {determinant}, so the solution is unique. "
            f"It gives x = {x} and y = {y}. Checking, the first left side is "
            f"{a*x+b*y}, equal to {rhs1}, and the second is {c*x+d*y}, equal to {rhs2}. "
            f"The solution is x = {x} and y = {y}."
        )
    else:
        raise ValueError(f"unsupported training family {family}")
    return f"Relevant ideas: {CONCEPTS[family]}\nReasoning: {body}"


def frozen_prompts() -> set[str]:
    prompts: set[str] = set()
    for split in ("dev", "test"):
        path = DATA / f"{split}.prompts.jsonl"
        for line in path.read_text().splitlines():
            if line.strip():
                prompts.add(json.loads(line)["prompt"])
    return prompts


def build(seed: int, count_per_family: int, forbidden: set[str]) -> list[dict]:
    collected: dict[str, dict[str, Instance]] = {family: {} for family in CONCEPTS}
    draw_count = min(140, max(60, count_per_family * 2))
    for offset in range(50):
        instances = generate_instances(
            seed=seed + offset,
            dev_per_family=draw_count,
            test_per_family=0,
        )
        for instance in instances:
            if instance.prompt not in forbidden:
                collected[instance.family].setdefault(instance.prompt, instance)
        if all(len(values) >= count_per_family for values in collected.values()):
            break
    if not all(len(values) >= count_per_family for values in collected.values()):
        counts = {family: len(values) for family, values in collected.items()}
        raise RuntimeError(f"insufficient disjoint synthetic prompts: {counts}")

    rows = []
    for family, values in collected.items():
        ranked = sorted(values.values(), key=lambda item: hashlib.sha256(f"{seed}:{item.prompt}".encode()).hexdigest())
        for instance in ranked[:count_per_family]:
            rows.append(
                {
                    "prompt": "Problem: " + instance.prompt + "\nAnswer:\n",
                    "completion": solution(instance),
                    "metadata": {
                        "source": "deterministic-nl-synthetic-v1",
                        "family": family,
                        "synthetic_id": instance.id,
                    },
                }
            )
    random.Random(seed).shuffle(rows)
    return rows


def row_hash(rows: list[dict]) -> str:
    payload = "".join(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n" for row in rows)
    return hashlib.sha256(payload.encode()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--train-per-family", type=int, default=60)
    parser.add_argument("--valid-per-family", type=int, default=10)
    parser.add_argument("--test-per-family", type=int, default=10)
    args = parser.parse_args()

    fixed = frozen_prompts()
    specs = {
        "train": (20260720, args.train_per_family),
        "valid": (20260721, args.valid_per_family),
        "test": (20260722, args.test_per_family),
    }
    split_rows: dict[str, list[dict]] = {}
    seen_prompts = set(fixed)
    for split, (seed, count) in specs.items():
        rows = build(seed, count, seen_prompts)
        row_prompts = {
            row["prompt"].removeprefix("Problem: ").removesuffix("\nAnswer:\n")
            for row in rows
        }
        if len(row_prompts) != len(rows) or row_prompts & seen_prompts:
            raise ValueError(f"duplicate or cross-split prompt in {split}")
        split_rows[split] = rows
        seen_prompts.update(row_prompts)

    args.output.mkdir(parents=True, exist_ok=True)
    for split, rows in split_rows.items():
        with (args.output / f"{split}.jsonl").open("w", encoding="utf-8") as handle:
            for row in rows:
                handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
    manifest = {
        "schema_version": 1,
        "purpose": "synthetic natural-language supervision; disjoint from frozen deterministic benchmark prompts",
        "formal_data_read": False,
        "seeds": {split: seed for split, (seed, _count) in specs.items()},
        "counts": {split: len(rows) for split, rows in split_rows.items()},
        "sha256": {split: row_hash(rows) for split, rows in split_rows.items()},
        "families": sorted(CONCEPTS),
        "frozen_benchmark_prompts_excluded": len(fixed),
    }
    (args.output / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
