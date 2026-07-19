#!/usr/bin/env python3
"""Emit Lean certificates only for semantically accepted atomic claims."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path


def load_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lean_name(identifier: str) -> str:
    return re.sub(r"[^A-Za-z0-9_]", "_", identifier)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--details", type=Path, required=True)
    parser.add_argument("--verifier", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--accept-field", default="semantic")
    args = parser.parse_args()

    accepted = {row["id"]: row for row in load_jsonl(args.details) if row[args.accept_field]}
    private = {row["id"]: row for row in load_jsonl(args.verifier)}
    lines = [
        "import Mathlib",
        "",
        "namespace AtomicClaimCertificates",
        "",
        "theorem linearCombinationIffGcdDvd (a b c : ℤ) :",
        "    (∃ x y : ℤ, c = a * x + b * y) ↔ ((Int.gcd a b : ℤ) ∣ c) := by",
        "  constructor",
        "  · rintro ⟨x, y, rfl⟩",
        "    exact Int.dvd_add (dvd_mul_of_dvd_left (Int.gcd_dvd_left a b) x)",
        "      (dvd_mul_of_dvd_left (Int.gcd_dvd_right a b) y)",
        "  · rintro ⟨k, rfl⟩",
        "    refine ⟨Int.gcdA a b * k, Int.gcdB a b * k, ?_⟩",
        "    rw [Int.gcd_eq_gcd_ab]",
        "    ring",
        "",
    ]
    trace_step_certificates = 0
    for identifier in sorted(accepted):
        row = private[identifier]
        if row["family"] not in {"diophantine_solvability", "diophantine_euclidean_trace"}:
            raise ValueError("this first atomic certificate emitter handles the Diophantine specialist only")
        params = row["parameters"]
        name = lean_name(identifier)
        a, b, c, gcd_value = params["a"], params["b"], params["c"], params["gcd"]
        lines.extend(
            [
                f"theorem {name}_gcd : Nat.gcd {a} {b} = {gcd_value} := by",
                "  norm_num [Nat.gcd]",
                "",
            ]
        )
        if row["family"] == "diophantine_euclidean_trace":
            steps = re.findall(
                r"Euclidean step: (-?\d+) = (-?\d+) times (-?\d+) plus (-?\d+)\.",
                accepted[identifier]["response"],
            )
            for step_index, (dividend, quotient, divisor, remainder) in enumerate(steps):
                lines.extend(
                    [
                        f"theorem {name}_step_{step_index} : ({dividend} : ℤ) = {quotient} * {divisor} + {remainder} := by",
                        "  norm_num",
                        "",
                    ]
                )
                trace_step_certificates += 1
        proposition = f"({gcd_value} : ℤ) ∣ ({c} : ℤ)"
        if not params["solvable"]:
            proposition = "¬ " + proposition
        lines.extend([f"theorem {name}_divides : {proposition} := by", "  norm_num", ""])
        conclusion = f"∃ x y : ℤ, ({c} : ℤ) = ({a} : ℤ) * x + ({b} : ℤ) * y"
        if not params["solvable"]:
            conclusion = "¬ (" + conclusion + ")"
        lines.append(f"theorem {name}_conclusion : {conclusion} := by")
        lines.append(f"  have hgcd : (Int.gcd ({a} : ℤ) ({b} : ℤ) : ℤ) = {gcd_value} := by norm_num [Int.gcd]")
        if params["solvable"]:
            lines.extend(
                [
                    f"  apply (linearCombinationIffGcdDvd ({a} : ℤ) ({b} : ℤ) ({c} : ℤ)).2",
                    f"  simpa [hgcd] using {name}_divides",
                ]
            )
        else:
            lines.extend(
                [
                    "  intro h",
                    f"  have hd := (linearCombinationIffGcdDvd ({a} : ℤ) ({b} : ℤ) ({c} : ℤ)).1 h",
                    "  rw [hgcd] at hd",
                    f"  exact {name}_divides hd",
                ]
            )
        lines.append("")
    lines.extend(["end AtomicClaimCertificates", ""])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("\n".join(lines), encoding="utf-8")
    manifest = {
        "accepted_claims": len(accepted),
        "accept_field": args.accept_field,
        "trace_step_certificates": trace_step_certificates,
        "details_sha256": sha256(args.details),
        "verifier_sha256": sha256(args.verifier),
        "certificate_sha256": sha256(args.output),
    }
    args.output.with_suffix(".manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
