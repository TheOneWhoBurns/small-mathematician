#!/usr/bin/env python3
"""Emit Lean certificates for verifier-strict natural-language model answers."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def z(value: int) -> str:
    return str(value) if value >= 0 else f"({value})"


def theorem_name(example_id: str) -> str:
    return "cert_" + re.sub(r"[^A-Za-z0-9_]", "_", example_id)


def certificate(example_id: str, family: str, verifier: dict) -> str | None:
    name = theorem_name(example_id)
    if family == "integer_expression":
        a, b, c, d = verifier["operands"]
        answer = verifier["answer"]
        return f"theorem {name} : (({a} + {b}) * {c} - {d} : ℤ) = {answer} := by\n  norm_num\n"
    if family == "modular_inverse":
        value = verifier["value"]
        modulus = verifier["modulus"]
        inverse = verifier["inverse"]
        return (
            f"theorem {name} : ({value} * {inverse}) % {modulus} = 1 ∧ "
            f"{inverse} < {modulus} := by\n  norm_num\n"
        )
    if family == "quadratic_integer_roots":
        linear = verifier["linear"]
        constant = verifier["constant"]
        r1, r2 = verifier["roots"]
        poly1 = f"({z(r1)} : ℤ)^2 + {z(linear)} * {z(r1)} + {z(constant)}"
        poly2 = f"({z(r2)} : ℤ)^2 + {z(linear)} * {z(r2)} + {z(constant)}"
        polyx = f"x^2 + {z(linear)} * x + {z(constant)}"
        return (
            f"theorem {name} : ({poly1} = 0) ∧ ({poly2} = 0) ∧ "
            f"(∀ x : ℤ, {polyx} = 0 → x = {z(r1)} ∨ x = {z(r2)}) := by\n"
            "  constructor\n"
            "  · norm_num\n"
            "  constructor\n"
            "  · norm_num\n"
            "  · intro x hx\n"
            f"    have hprod : (x - {z(r1)}) * (x - {z(r2)}) = 0 := by nlinarith\n"
            "    rcases mul_eq_zero.mp hprod with h | h\n"
            "    · left; linarith\n"
            "    · right; linarith\n"
        )
    if family == "linear_system":
        a, b, c, d = (verifier[key] for key in ("a", "b", "c", "d"))
        rhs1, rhs2 = verifier["rhs1"], verifier["rhs2"]
        x, y = verifier["x"], verifier["y"]
        return (
            f"theorem {name} : ({z(a)} * {z(x)} + {z(b)} * {z(y)} = {z(rhs1)}) ∧ "
            f"({z(c)} * {z(x)} + {z(d)} * {z(y)} = {z(rhs2)}) ∧ "
            f"(∀ u v : ℤ, {z(a)} * u + {z(b)} * v = {z(rhs1)} → "
            f"{z(c)} * u + {z(d)} * v = {z(rhs2)} → u = {z(x)} ∧ v = {z(y)}) := by\n"
            "  constructor\n"
            "  · norm_num\n"
            "  constructor\n"
            "  · norm_num\n"
            "  · intro u v h1 h2\n"
            "    constructor <;> nlinarith\n"
        )
    return None


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--predictions", type=Path, required=True)
    parser.add_argument("--details", type=Path, required=True)
    parser.add_argument("--verifier", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    predictions = {row["id"]: row for row in read_jsonl(args.predictions)}
    details = read_jsonl(args.details)
    verifiers = {row["id"]: row for row in read_jsonl(args.verifier)}
    strict = [row for row in details if row["strict_pass"]]

    declarations: list[str] = []
    certified_ids: list[str] = []
    unsupported_ids: list[str] = []
    for row in strict:
        example_id = row["id"]
        if example_id not in predictions or example_id not in verifiers:
            raise ValueError(f"missing joined row for {example_id}")
        declaration = certificate(example_id, row["family"], verifiers[example_id]["verifier"])
        if declaration is None:
            unsupported_ids.append(example_id)
            continue
        declarations.append(declaration)
        certified_ids.append(example_id)

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        "import Mathlib\n\nnamespace SmallMathematicianCertificates\n\n"
        + "\n".join(declarations)
        + "\nend SmallMathematicianCertificates\n"
    )
    manifest = {
        "schema_version": 1,
        "predictions": str(args.predictions),
        "predictions_sha256": sha256(args.predictions),
        "details": str(args.details),
        "details_sha256": sha256(args.details),
        "verifier": str(args.verifier),
        "verifier_sha256": sha256(args.verifier),
        "strict_passes": len(strict),
        "lean_certificates_emitted": len(certified_ids),
        "certified_ids": certified_ids,
        "unsupported_strict_ids": unsupported_ids,
        "contract": "Each theorem restates the exact private verifier claim for a model response already accepted by the strict parser; Lean independently checks the arithmetic claim, not the natural-language parser.",
    }
    args.output.with_suffix(".manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
