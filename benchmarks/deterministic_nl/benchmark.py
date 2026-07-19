#!/usr/bin/env python3
"""Deterministic natural-language mathematical reasoning benchmark core."""

from __future__ import annotations

import hashlib
import json
import math
import random
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Iterable


ROOT = Path(__file__).resolve().parent
DATA = ROOT / "data"
SCHEMA_VERSION = 1
DEFAULT_SEED = 20260718

SHARED_FAMILIES = (
    "integer_expression",
    "gcd_bezout",
    "modular_inverse",
    "quadratic_integer_roots",
    "linear_system",
)
TEST_ONLY_FAMILIES = ("chinese_remainder", "polynomial_remainder")
ALL_FAMILIES = SHARED_FAMILIES + TEST_ONLY_FAMILIES

FORBIDDEN_MODEL_TEXT = (
    "lean",
    "mathlib",
    "proof state",
    "tactic",
    "by simp",
    "by omega",
    "#check",
    ":= by",
)


@dataclass(frozen=True)
class Instance:
    id: str
    split: str
    family: str
    prompt: str
    verifier: dict[str, Any]

    def public(self) -> dict[str, Any]:
        return {
            "id": self.id,
            "split": self.split,
            "family": self.family,
            "prompt": self.prompt,
            "schema_version": SCHEMA_VERSION,
        }

    def private(self) -> dict[str, Any]:
        return {
            "id": self.id,
            "split": self.split,
            "family": self.family,
            "verifier": self.verifier,
            "schema_version": SCHEMA_VERSION,
        }


def _rng(seed: int, split: str, family: str) -> random.Random:
    digest = hashlib.sha256(f"{seed}:{split}:{family}".encode()).digest()
    return random.Random(int.from_bytes(digest[:8], "big"))


def _instance_id(split: str, family: str, index: int, prompt: str) -> str:
    digest = hashlib.sha256(prompt.encode()).hexdigest()[:10]
    return f"dnl-v{SCHEMA_VERSION}-{split}-{family}-{index:03d}-{digest}"


def _extended_gcd(a: int, b: int) -> tuple[int, int, int]:
    old_r, r = a, b
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r:
        quotient = old_r // r
        old_r, r = r, old_r - quotient * r
        old_s, s = s, old_s - quotient * s
        old_t, t = t, old_t - quotient * t
    return old_r, old_s, old_t


def _coprime_pair(rng: random.Random, low: int, high: int) -> tuple[int, int]:
    while True:
        a, b = rng.randint(low, high), rng.randint(low, high)
        if a != b and math.gcd(a, b) == 1:
            return a, b


def _make_integer_expression(rng: random.Random, split: str) -> tuple[str, dict[str, Any]]:
    if split == "dev":
        a, b, c, d = (rng.randint(2, 20) for _ in range(4))
        expression = f"the quantity {a} plus {b}, multiplied by {c}, and then reduced by {d}"
        answer = (a + b) * c - d
    else:
        a, b, c, d, e = (rng.randint(21, 180) for _ in range(5))
        expression = (
            f"the difference between {a} and {b}, multiplied by the sum of {c} and {d}, "
            f"and then increased by {e}"
        )
        answer = (a - b) * (c + d) + e
    prompt = (
        f"Evaluate {expression}. Explain your calculation briefly. "
        "End with a sentence of the form 'The answer is N.'"
    )
    return prompt, {"answer": answer, "operands": [a, b, c, d] if split == "dev" else [a, b, c, d, e]}


def _make_gcd_bezout(rng: random.Random, split: str) -> tuple[str, dict[str, Any]]:
    low, high = ((3, 35) if split == "dev" else (36, 180))
    p, q = _coprime_pair(rng, low, high)
    scale = rng.randint(2, 15 if split == "dev" else 60)
    a, b = scale * p, scale * q
    gcd_value, x, y = _extended_gcd(a, b)
    prompt = (
        f"Find the greatest common divisor of {a} and {b}. Also give integer coefficients x and y "
        f"that certify the result by making {a} times x plus {b} times y equal to the greatest "
        "common divisor. Explain your reasoning briefly. End with: "
        "'The greatest common divisor is G; coefficients x = X and y = Y certify it.'"
    )
    return prompt, {"a": a, "b": b, "gcd": gcd_value, "canonical_x": x, "canonical_y": y}


def _make_modular_inverse(rng: random.Random, split: str) -> tuple[str, dict[str, Any]]:
    low, high = ((11, 80) if split == "dev" else (81, 500))
    modulus = rng.randint(low, high)
    while True:
        value = rng.randint(2, modulus - 1)
        if math.gcd(value, modulus) == 1:
            break
    inverse = pow(value, -1, modulus)
    prompt = (
        f"Find the least nonnegative multiplicative inverse of {value} modulo {modulus}. "
        f"In other words, find the least nonnegative integer which, when multiplied by {value}, "
        f"leaves remainder 1 after division by {modulus}. Explain your reasoning briefly. "
        "End with a sentence of the form 'The inverse is I.'"
    )
    return prompt, {"value": value, "modulus": modulus, "inverse": inverse}


def _make_quadratic(rng: random.Random, split: str) -> tuple[str, dict[str, Any]]:
    if split == "dev":
        roots = [value for value in range(-9, 10) if value != 0]
    else:
        roots = [value for value in range(-35, 36) if abs(value) >= 10]
    r1, r2 = rng.sample(roots, 2)
    linear = -(r1 + r2)
    constant = r1 * r2
    linear_phrase = f"plus {linear} times x" if linear >= 0 else f"minus {abs(linear)} times x"
    constant_phrase = f"plus {constant}" if constant >= 0 else f"minus {abs(constant)}"
    prompt = (
        f"Find both integer roots of the equation x squared {linear_phrase} {constant_phrase} equals zero. "
        "Explain how you know both roots are correct. End with: 'The integer roots are R and S.'"
    )
    return prompt, {"linear": linear, "constant": constant, "roots": sorted((r1, r2))}


def _make_linear_system(rng: random.Random, split: str) -> tuple[str, dict[str, Any]]:
    coefficient_bound = 6 if split == "dev" else 16
    solution_bound = 10 if split == "dev" else 40
    coefficient_choices = [
        value
        for value in range(-coefficient_bound, coefficient_bound + 1)
        if value != 0 and (split == "dev" or abs(value) >= 7)
    ]
    solution_choices = [
        value
        for value in range(-solution_bound, solution_bound + 1)
        if split == "dev" or abs(value) >= 11
    ]
    while True:
        a, b, c, d = (rng.choice(coefficient_choices) for _ in range(4))
        determinant = a * d - b * c
        if determinant and all(value != 0 for value in (a, b, c, d)):
            break
    x, y = rng.choice(solution_choices), rng.choice(solution_choices)
    rhs1, rhs2 = a * x + b * y, c * x + d * y
    def equation(left_x: int, left_y: int, right: int) -> str:
        joiner = "plus" if left_y >= 0 else "minus"
        return f"{left_x} times x {joiner} {abs(left_y)} times y equals {right}"

    prompt = (
        f"Find the unique integer solution x and y to these two equations: {equation(a, b, rhs1)}; "
        f"and {equation(c, d, rhs2)}. Explain your reasoning briefly. "
        "End with: 'The solution is x = X and y = Y.'"
    )
    return prompt, {"a": a, "b": b, "c": c, "d": d, "rhs1": rhs1, "rhs2": rhs2, "x": x, "y": y}


def _make_chinese_remainder(rng: random.Random, split: str) -> tuple[str, dict[str, Any]]:
    del split
    mod1, mod2 = _coprime_pair(rng, 7, 45)
    residue1 = rng.randrange(mod1)
    residue2 = rng.randrange(mod2)
    answer = next(
        value for value in range(mod1 * mod2) if value % mod1 == residue1 and value % mod2 == residue2
    )
    prompt = (
        f"Find the least nonnegative integer that leaves remainder {residue1} when divided by {mod1} "
        f"and remainder {residue2} when divided by {mod2}. Explain why your integer satisfies both "
        "conditions. End with a sentence of the form 'The answer is N.'"
    )
    return prompt, {"mod1": mod1, "mod2": mod2, "residue1": residue1, "residue2": residue2, "answer": answer}


def _make_polynomial_remainder(rng: random.Random, split: str) -> tuple[str, dict[str, Any]]:
    del split
    coefficients = [rng.randint(-12, 12) for _ in range(4)]
    while coefficients[0] == 0:
        coefficients[0] = rng.randint(-12, 12)
    point = rng.choice([value for value in range(-9, 10) if value not in (0, 1)])
    a, b, c, d = coefficients
    answer = ((a * point + b) * point + c) * point + d
    def signed_term(coefficient: int, term: str) -> str:
        joiner = "plus" if coefficient >= 0 else "minus"
        return f"{joiner} {abs(coefficient)} times {term}"

    divisor = f"x minus {point}" if point > 0 else f"x plus {abs(point)}"
    prompt = (
        f"A polynomial is given by p of x equals {a} times x cubed {signed_term(b, 'x squared')} "
        f"{signed_term(c, 'x')} {'plus' if d >= 0 else 'minus'} {abs(d)}. Find the remainder when this "
        f"polynomial is divided by {divisor}. "
        "Explain your reasoning briefly. End with a sentence of the form 'The answer is N.'"
    )
    return prompt, {"coefficients": coefficients, "point": point, "answer": answer}


GENERATORS: dict[str, Callable[[random.Random, str], tuple[str, dict[str, Any]]]] = {
    "integer_expression": _make_integer_expression,
    "gcd_bezout": _make_gcd_bezout,
    "modular_inverse": _make_modular_inverse,
    "quadratic_integer_roots": _make_quadratic,
    "linear_system": _make_linear_system,
    "chinese_remainder": _make_chinese_remainder,
    "polynomial_remainder": _make_polynomial_remainder,
}


def generate_instances(
    seed: int = DEFAULT_SEED,
    dev_per_family: int = 12,
    test_per_family: int = 20,
) -> list[Instance]:
    instances: list[Instance] = []
    for split, families, count in (
        ("dev", SHARED_FAMILIES, dev_per_family),
        ("test", ALL_FAMILIES, test_per_family),
    ):
        for family in families:
            rng = _rng(seed, split, family)
            seen_prompts: set[str] = set()
            index = 0
            attempts = 0
            while index < count:
                attempts += 1
                if attempts > count * 100:
                    raise RuntimeError(f"could not produce {count} unique instances for {split}/{family}")
                prompt, verifier = GENERATORS[family](rng, split)
                if prompt in seen_prompts:
                    continue
                seen_prompts.add(prompt)
                instances.append(
                    Instance(
                        id=_instance_id(split, family, index, prompt),
                        split=split,
                        family=family,
                        prompt=prompt,
                        verifier=verifier,
                    )
                )
                index += 1
    return instances


INTEGER = r"([+-]?\d+)"
ANSWER_RE = re.compile(rf"\bthe\s+answer\s+is\s+{INTEGER}\b", re.IGNORECASE)
INVERSE_RE = re.compile(rf"\bthe\s+inverse\s+is\s+{INTEGER}\b", re.IGNORECASE)
ROOTS_RE = re.compile(
    rf"\bthe\s+integer\s+roots\s+are\s+{INTEGER}\s+(?:and|,)\s*{INTEGER}\b",
    re.IGNORECASE,
)
SOLUTION_RE = re.compile(
    rf"\bthe\s+solution\s+is\s+x\s*=\s*{INTEGER}\s+(?:and|,)\s*y\s*=\s*{INTEGER}\b",
    re.IGNORECASE,
)
GCD_RE = re.compile(
    rf"\bthe\s+greatest\s+common\s+divisor\s+is\s+{INTEGER}\s*;?\s*"
    rf"coefficients\s+x\s*=\s*{INTEGER}\s+(?:and|,)\s*y\s*=\s*{INTEGER}",
    re.IGNORECASE,
)


def _last_match(pattern: re.Pattern[str], response: str) -> re.Match[str] | None:
    matches = list(pattern.finditer(response))
    return matches[-1] if matches else None


def _reasoning_present(response: str, match: re.Match[str] | None) -> bool:
    if match is None:
        return False
    remainder = (response[: match.start()] + response[match.end() :]).strip()
    words = re.findall(r"\b[A-Za-z]+\b", remainder)
    return len(words) >= 4


def evaluate_response(instance: Instance, response: str) -> dict[str, Any]:
    response = response.strip()
    family, verifier = instance.family, instance.verifier
    pattern = {
        "integer_expression": ANSWER_RE,
        "gcd_bezout": GCD_RE,
        "modular_inverse": INVERSE_RE,
        "quadratic_integer_roots": ROOTS_RE,
        "linear_system": SOLUTION_RE,
        "chinese_remainder": ANSWER_RE,
        "polynomial_remainder": ANSWER_RE,
    }[family]
    match = _last_match(pattern, response)
    result: dict[str, Any] = {
        "id": instance.id,
        "split": instance.split,
        "family": family,
        "format_valid": match is not None,
        "reasoning_present": _reasoning_present(response, match),
        "answer_correct": False,
        "certificate_valid": None,
        "strict_pass": False,
    }
    if match is None:
        result["error"] = "required natural-language answer sentence not found"
        return result
    values = tuple(int(group) for group in match.groups())
    if family in {"integer_expression", "polynomial_remainder"}:
        result["answer_correct"] = values[0] == verifier["answer"]
    elif family == "chinese_remainder":
        value = values[0]
        result["answer_correct"] = (
            value == verifier["answer"]
            and 0 <= value < verifier["mod1"] * verifier["mod2"]
            and value % verifier["mod1"] == verifier["residue1"]
            and value % verifier["mod2"] == verifier["residue2"]
        )
        result["certificate_valid"] = result["answer_correct"]
    elif family == "modular_inverse":
        inverse = values[0]
        result["answer_correct"] = inverse == verifier["inverse"]
        result["certificate_valid"] = (
            0 <= inverse < verifier["modulus"]
            and verifier["value"] * inverse % verifier["modulus"] == 1
        )
    elif family == "quadratic_integer_roots":
        roots = sorted(values)
        result["answer_correct"] = roots == verifier["roots"]
        result["certificate_valid"] = all(
            root * root + verifier["linear"] * root + verifier["constant"] == 0 for root in roots
        ) and roots[0] != roots[1]
    elif family == "linear_system":
        x, y = values
        result["answer_correct"] = x == verifier["x"] and y == verifier["y"]
        result["certificate_valid"] = (
            verifier["a"] * x + verifier["b"] * y == verifier["rhs1"]
            and verifier["c"] * x + verifier["d"] * y == verifier["rhs2"]
        )
    elif family == "gcd_bezout":
        gcd_value, x, y = values
        result["answer_correct"] = gcd_value == math.gcd(verifier["a"], verifier["b"])
        result["certificate_valid"] = (
            gcd_value > 0
            and verifier["a"] * x + verifier["b"] * y == gcd_value
            and gcd_value == math.gcd(verifier["a"], verifier["b"])
        )
    result["strict_pass"] = bool(
        result["format_valid"]
        and result["answer_correct"]
        and result["reasoning_present"]
        and result["certificate_valid"] is not False
    )
    if not result["strict_pass"]:
        result["error"] = "parsed response failed one or more exact checks"
    return result


def oracle_response(instance: Instance) -> str:
    v = instance.verifier
    prefix = "I compute the requested quantities and check them in the original conditions. "
    if instance.family in {"integer_expression", "polynomial_remainder", "chinese_remainder"}:
        return prefix + f"The answer is {v['answer']}."
    if instance.family == "modular_inverse":
        return prefix + f"The inverse is {v['inverse']}."
    if instance.family == "quadratic_integer_roots":
        r1, r2 = v["roots"]
        return prefix + f"The integer roots are {r1} and {r2}."
    if instance.family == "linear_system":
        return prefix + f"The solution is x = {v['x']} and y = {v['y']}."
    if instance.family == "gcd_bezout":
        return (
            prefix
            + f"The greatest common divisor is {v['gcd']}; coefficients x = {v['canonical_x']} "
            + f"and y = {v['canonical_y']} certify it."
        )
    raise ValueError(instance.family)


def load_instances(split: str, data_dir: Path = DATA) -> list[Instance]:
    public_path = data_dir / f"{split}.prompts.jsonl"
    private_path = data_dir / f"{split}.verifier.jsonl"
    with public_path.open(encoding="utf-8") as handle:
        public = {row["id"]: row for line in handle if (row := json.loads(line))}
    with private_path.open(encoding="utf-8") as handle:
        private = {row["id"]: row for line in handle if (row := json.loads(line))}
    if public.keys() != private.keys():
        raise ValueError(f"public/private IDs disagree for split {split}")
    return [
        Instance(
            id=row["id"],
            split=row["split"],
            family=row["family"],
            prompt=row["prompt"],
            verifier=private[row["id"]]["verifier"],
        )
        for row in public.values()
    ]


def write_jsonl(path: Path, rows: Iterable[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")


def validate_model_boundary(instances: Iterable[Instance]) -> None:
    for instance in instances:
        lowered = instance.prompt.lower()
        for forbidden in FORBIDDEN_MODEL_TEXT:
            if forbidden in lowered:
                raise ValueError(f"forbidden model-facing text {forbidden!r} in {instance.id}")
