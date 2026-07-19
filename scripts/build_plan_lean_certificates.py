#!/usr/bin/env python3
"""Build Lean certificates from typed claims parsed from natural-language plans.

Problem parameters come from the private verifier row, but every proposed
deduction/witness in a certificate comes from ``parsed`` in the result row.
The builder recomputes all claims and aborts before writing if any are missing
or false.  It never replaces a bad model claim with a canonical answer.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
from pathlib import Path
from typing import Any


SUPPORTED_FAMILIES = {
    "polynomial_value_obstruction",
    "diophantine_solvability",
    "modular_period_prime_filter",
    "finite_double_count",
    "finite_recurrence_period",
}


class UnsupportedCertificate(ValueError):
    """A sound certificate shape exists, but this concrete row is outside its bound."""


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def need(obj: dict[str, Any], key: str, kind: type = int) -> Any:
    if key not in obj:
        raise ValueError(f"missing required parsed claim {key!r}")
    value = obj[key]
    if kind is int and (not isinstance(value, int) or isinstance(value, bool)):
        raise ValueError(f"claim {key!r} must be an integer")
    if kind is bool and not isinstance(value, bool):
        raise ValueError(f"claim {key!r} must be a boolean")
    if kind is list and not isinstance(value, list):
        raise ValueError(f"claim {key!r} must be a list")
    if kind is dict and not isinstance(value, dict):
        raise ValueError(f"claim {key!r} must be an object")
    return value


def nat_list(values: Any, key: str) -> list[int]:
    if not isinstance(values, list) or any(
        not isinstance(x, int) or isinstance(x, bool) or x < 0 for x in values
    ):
        raise ValueError(f"claim {key!r} must be a list of natural numbers")
    return values


def instance_of(private_row: dict[str, Any]) -> dict[str, Any]:
    value = private_row.get(
        "parameters", private_row.get("instance", private_row.get("problem"))
    )
    if not isinstance(value, dict):
        raise ValueError("private row needs an object-valued 'instance'")
    return value


def parsed_of(result_row: dict[str, Any]) -> dict[str, Any]:
    value = result_row.get("parsed_claims", result_row.get("parsed"))
    if isinstance(value, dict):
        return value
    if not isinstance(value, list):
        raise ValueError("result row needs a list-valued 'parsed_claims'")
    claims: dict[str, Any] = {}
    positions: list[int] = []
    for claim in value:
        if not isinstance(claim, dict) or not isinstance(claim.get("kind"), str):
            raise ValueError("each parsed claim needs string 'kind' and a 'value'")
        kind = claim["kind"]
        if kind in claims:
            raise ValueError(f"duplicate parsed claim kind {kind!r}")
        if "value" not in claim:
            raise ValueError(f"parsed claim {kind!r} has no value")
        position = claim.get("position")
        if not isinstance(position, int) or isinstance(position, bool) or position < 0:
            raise ValueError(f"parsed claim {kind!r} has invalid position")
        positions.append(position)
        claims[kind] = claim["value"]
    if positions != sorted(positions) or len(set(positions)) != len(positions):
        raise ValueError("parsed claim positions must be unique and increasing")
    return claims


def z(value: int) -> str:
    return str(value) if value >= 0 else f"({value})"


def n(value: int) -> str:
    if value < 0:
        raise ValueError("Lean natural-number literal cannot be negative")
    return str(value)


def lean_nat_list(values: list[int]) -> str:
    return "[" + ", ".join(str(value) for value in values) + "]"


def lean_state(value: Any, key: str) -> tuple[int, int]:
    values = nat_list(value, key)
    if len(values) != 2:
        raise ValueError(f"claim {key!r} must contain two coordinates")
    return values[0], values[1]


def theorem_name(example_id: str) -> str:
    return "vp_" + re.sub(r"[^A-Za-z0-9_]", "_", example_id)


def require_equal(actual: Any, expected: Any, label: str) -> None:
    if actual != expected:
        raise ValueError(f"false claim {label}: parsed {actual!r}, recomputed {expected!r}")


def certificate_polynomial(name: str, p: dict[str, Any], c: dict[str, Any]) -> str:
    u, v = (need(p, key) for key in ("u", "v"))
    A, B = (need(p, key) for key in ("a_value", "b_value"))
    d = need(c, "input_difference")
    e = need(c, "value_difference")
    principle = need(c, "divisibility_principle", dict)
    remainder_claim = need(c, "remainder", dict)
    conclusion = need(c, "conclusion", dict)
    principle_divisor = need(principle, "divisor")
    modulus = need(remainder_claim, "modulus")
    remainder = need(remainder_claim, "remainder")
    can_exist = need(conclusion, "exists", bool)
    require_equal(d, v - u, "input_difference")
    require_equal(e, B - A, "value_difference")
    require_equal(principle_divisor, d, "divisibility_principle.divisor")
    require_equal(modulus, abs(d), "modulus")
    if modulus == 0:
        raise ValueError("polynomial rows with identical inputs are unsupported")
    require_equal(remainder, e % modulus, "remainder")
    require_equal(can_exist, remainder == 0, "can_exist")

    facts = (
        f"theorem {name}_differences : (({z(v)} - {z(u)} : ℤ) = {z(d)}) ∧ "
        f"(({z(B)} - {z(A)} : ℤ) = {z(e)}) := by\n  norm_num\n\n"
        f"theorem {name}_remainder : ({z(e)} : ℤ) % {n(modulus)} = {n(remainder)} := by\n"
        "  norm_num\n\n"
    )
    statement = (
        f"∃ P : Polynomial ℤ, P.eval {z(u)} = {z(A)} ∧ P.eval {z(v)} = {z(B)}"
    )
    if can_exist:
        q = need(c, "quotient")
        require_equal(q * d, e, "quotient")
        proof = (
            f"theorem {name} : {statement} := by\n"
            f"  refine ⟨linearPolynomialWitness {z(q)} {z(u)} {z(A)}, ?_, ?_⟩ <;>\n"
            "    norm_num [linearPolynomialWitness]\n"
        )
    else:
        if "quotient" in c:
            raise ValueError("impossible polynomial row must not claim an integer quotient")
        proof = (
            f"theorem {name} : ¬ ({statement}) := by\n"
            "  apply no_polynomial_with_values_of_not_dvd\n"
            "  norm_num\n"
        )
    return facts + proof


def certificate_diophantine(name: str, p: dict[str, Any], c: dict[str, Any]) -> str:
    a, b, rhs = (need(p, key) for key in ("a", "b", "c"))
    g = need(c, "gcd")
    divides_claim = need(c, "divides", dict)
    conclusion = need(c, "conclusion", dict)
    divides = need(divides_claim, "holds", bool)
    has_solution = need(conclusion, "solvable", bool)
    require_equal(g, math.gcd(a, b), "gcd")
    require_equal(need(divides_claim, "gcd"), g, "divides.gcd")
    require_equal(need(divides_claim, "c"), rhs, "divides.c")
    require_equal(divides, rhs % g == 0 if g else rhs == 0, "divides")
    require_equal(has_solution, divides, "has_solution")
    facts = (
        f"theorem {name}_gcd : Nat.gcd ({z(a)} : ℤ).natAbs ({z(b)} : ℤ).natAbs = {n(g)} := by\n"
        "  norm_num [Int.natAbs]\n\n"
    )
    if "bezout" in c:
        bezout = need(c, "bezout", dict)
        bezout_u = need(bezout, "u")
        bezout_v = need(bezout, "v")
        require_equal(need(bezout, "gcd"), g, "bezout.gcd")
        require_equal(a * bezout_u + b * bezout_v, g, "Bezout coefficients")
        facts += (
            f"theorem {name}_bezout : ({z(a)} : ℤ) * {z(bezout_u)} + "
            f"{z(b)} * {z(bezout_v)} = {n(g)} := by\n  norm_num\n\n"
        )
    statement = f"∃ x y : ℤ, {z(a)} * x + {z(b)} * y = {z(rhs)}"
    if has_solution:
        if "bezout" not in c:
            raise ValueError("solvable Diophantine row needs parsed Bezout coefficients")
        solution = need(c, "solution", dict)
        x = need(solution, "x")
        y = need(solution, "y")
        require_equal(need(solution, "c"), rhs, "solution.c")
        require_equal(a * x + b * y, rhs, "scaled solution")
        return facts + (
            f"theorem {name} : {statement} := by\n"
            f"  exact ⟨{z(x)}, {z(y)}, by norm_num⟩\n"
        )
    if "solution" in c:
        raise ValueError("unsolvable Diophantine row must not claim a solution")
    invariant = need(c, "combination_invariant", dict)
    require_equal(need(invariant, "a"), a, "combination_invariant.a")
    require_equal(need(invariant, "b"), b, "combination_invariant.b")
    require_equal(need(invariant, "gcd"), g, "combination_invariant.gcd")
    return facts + (
        f"theorem {name} : ¬ ({statement}) := by\n"
        "  apply no_diophantine_solution_of_common_dvd (g := " + n(g) + ")\n"
        "  · norm_num\n  · norm_num\n  · norm_num\n"
    )


def is_prime(value: int) -> bool:
    if value < 2:
        return False
    return all(value % divisor for divisor in range(2, math.isqrt(value) + 1))


def multiplicative_order(base: int, modulus: int) -> int:
    if math.gcd(base, modulus) != 1:
        raise ValueError("base is not invertible modulo modulus")
    for period in range(1, modulus * modulus + 1):
        if pow(base, period, modulus) == 1:
            return period
    raise ValueError("multiplicative order search bound exhausted")


def certificate_modular(name: str, p: dict[str, Any], c: dict[str, Any]) -> str:
    base, modulus, target, lo, hi = (
        need(p, key)
        for key in ("base", "modulus", "target_residue", "range_low", "range_high")
    )
    if modulus <= 1 or min(base, target, lo, hi) < 0 or lo > hi:
        raise ValueError("invalid bounded modular instance")
    period_claim = need(c, "period", dict)
    classes_claim = need(c, "classes", dict)
    conclusion = need(c, "conclusion", dict)
    period = need(period_claim, "period")
    require_equal(need(period_claim, "base"), base, "period.base")
    require_equal(need(period_claim, "modulus"), modulus, "period.modulus")
    classes = nat_list(need(classes_claim, "classes", list), "classes.classes")
    require_equal(need(classes_claim, "period"), period, "classes.period")
    conclusion_exponents = nat_list(
        need(conclusion, "exponents", list), "conclusion.exponents"
    )
    if period <= 0:
        raise ValueError("period must be positive")
    require_equal(period, multiplicative_order(base, modulus), "minimal period")
    expected_classes = [k for k in range(period) if pow(base, k, modulus) == target]
    require_equal(classes, expected_classes, "target_classes")
    prefix = (
        f"theorem {name}_period : powResidue {n(base)} {n(modulus)} {n(period)} = 1 := by\n"
        "  native_decide\n\n"
        f"theorem {name}_periodic (exponent : ℕ) :\n"
        f"    powResidue {n(base)} {n(modulus)} (exponent + {n(period)}) = "
        f"powResidue {n(base)} {n(modulus)} exponent := by\n"
        f"  exact powResidue_add_period {name}_period\n\n"
        f"theorem {name}_minimal_period : properPeriodWitnesses {n(base)} "
        f"{n(modulus)} {n(period)} = [] := by\n  native_decide\n\n"
        f"theorem {name}_classes : residueClasses {n(base)} {n(modulus)} {n(target)} "
        f"{n(period)} = {lean_nat_list(classes)} := by\n  native_decide\n\n"
    )
    if p.get("task_kind") != "prime_filter":
        require_equal(conclusion_exponents, classes, "conclusion.exponents")
        return prefix + (
            f"theorem {name} : residueClasses {n(base)} {n(modulus)} {n(target)} "
            f"{n(period)} = {lean_nat_list(conclusion_exponents)} := by\n"
            f"  exact {name}_classes\n"
        )
    candidates = nat_list(need(c, "prime_candidates", list), "prime_candidates")
    valid = nat_list(need(c, "intersection", list), "intersection")
    expected_candidates = [k for k in range(lo, hi + 1) if is_prime(k)]
    expected_valid = [k for k in expected_candidates if pow(base, k, modulus) == target]
    require_equal(candidates, expected_candidates, "prime_candidates")
    require_equal(valid, expected_valid, "valid_exponents")
    require_equal(conclusion_exponents, valid, "conclusion.exponents")
    return prefix + (
        f"theorem {name}_prime_range : primesInClosedRange {n(lo)} {n(hi)} = "
        f"{lean_nat_list(candidates)} := by\n  native_decide\n\n"
        f"theorem {name} : validPrimeExponents {n(base)} {n(modulus)} {n(target)} "
        f"{n(lo)} {n(hi)} = {lean_nat_list(valid)} := by\n  native_decide\n"
    )


def certificate_double_count(name: str, p: dict[str, Any], c: dict[str, Any]) -> str:
    universe_size = need(p, "universe")
    tuple_length = need(p, "tuple_length")
    if universe_size <= 0 or tuple_length < 0:
        raise ValueError("invalid double-count instance")
    total = need(c, "tuple_count")
    absent = need(c, "absent_count")
    contains = need(c, "contain_count")
    conclusion = need(c, "conclusion", dict)
    conclusion_sum = need(conclusion, "sum")
    expected_total = 2 ** (universe_size * tuple_length)
    expected_absent = 2 ** (tuple_length * (universe_size - 1))
    expected_contains = expected_total - expected_absent
    require_equal(total, expected_total, "total")
    require_equal(absent, expected_absent, "absent")
    require_equal(contains, expected_contains, "contains")
    # The exact finite enumeration is deliberately bounded.  Above this size a
    # generic combinatorial proof is needed; silently certifying only the closed
    # form would not certify the stated finite sum.
    if universe_size * tuple_length > 16:
        raise UnsupportedCertificate(
            "exact double-count enumeration exceeds 2^16 configurations"
        )
    prefix = (
        f"theorem {name}_total : Fintype.card (SubsetTuple {n(universe_size)} "
        f"{n(tuple_length)}) = "
        f"{n(total)} := by\n  native_decide\n\n"
        f"theorem {name}_absent : fixedElementAbsentConfigCount {n(universe_size)} "
        f"{n(tuple_length)} ⟨0, by norm_num⟩ = {n(absent)} := by\n"
        "  native_decide\n\n"
        f"theorem {name}_contains : {n(total)} - {n(absent)} = {n(contains)} := by\n"
        "  norm_num\n\n"
    )
    if not p.get("composition"):
        incidence_claim = need(c, "total_incidences", dict)
        incidences = need(incidence_claim, "total")
        require_equal(
            need(incidence_claim, "universe"),
            universe_size,
            "total_incidences.universe",
        )
        expected_incidences = universe_size * expected_contains
        require_equal(incidences, expected_incidences, "incidences")
        require_equal(conclusion_sum, incidences, "conclusion.sum")
        return prefix + (
            f"theorem {name} : enumeratedUnionIncidences {n(universe_size)} "
            f"{n(tuple_length)} = {n(incidences)} := by\n  native_decide\n"
        )
    class_claims = [
        need(c, "class_1_contribution", dict),
        need(c, "class_2_contribution", dict),
    ]
    class_claims.sort(key=lambda claim: need(claim, "class_id"))
    if [need(claim, "class_id") for claim in class_claims] != [1, 2]:
        raise ValueError("weighted double count needs exactly class ids 1 and 2")
    sizes = [need(claim, "size") for claim in class_claims]
    weights = [need(claim, "weight") for claim in class_claims]
    contributions = [need(claim, "contribution") for claim in class_claims]
    for index, claim in enumerate(class_claims):
        require_equal(need(claim, "contain_count"), contains, f"class {index + 1} contain_count")
        require_equal(
            contributions[index],
            sizes[index] * weights[index] * contains,
            f"class {index + 1} contribution",
        )
    require_equal(sum(sizes), universe_size, "class sizes")
    require_equal(sizes, p.get("class_sizes"), "class sizes from problem")
    require_equal(weights, p.get("class_weights"), "class weights from problem")
    require_equal(conclusion_sum, sum(contributions), "conclusion.sum")
    return prefix + (
        f"theorem {name}_class_1 : {n(sizes[0])} * {n(weights[0])} * "
        f"{n(contains)} = {n(contributions[0])} := by norm_num\n\n"
        f"theorem {name}_class_2 : {n(sizes[1])} * {n(weights[1])} * "
        f"{n(contains)} = {n(contributions[1])} := by norm_num\n\n"
        f"theorem {name} : enumeratedWeightedUnionIncidences {n(universe_size)} "
        f"{n(tuple_length)} {n(sizes[0])} {n(weights[0])} {n(weights[1])} = "
        f"{n(conclusion_sum)} := by\n  native_decide\n"
    )


def transition(instance: dict[str, Any], state: tuple[int, int]) -> tuple[int, int]:
    modulus = need(instance, "modulus")
    beta, gamma = (need(instance, key) for key in ("beta", "gamma"))
    x, y = state
    return (y % modulus, (x + beta * y + gamma) % modulus)


def state_at(instance: dict[str, Any], index: int) -> tuple[int, int]:
    state = lean_state(need(instance, "initial_state", list), "initial_state")
    for _ in range(index):
        state = transition(instance, state)
    return state


def certificate_recurrence(name: str, p: dict[str, Any], c: dict[str, Any]) -> str:
    modulus = need(p, "modulus")
    if modulus <= 0:
        raise ValueError("recurrence modulus must be positive")
    beta, gamma = (need(p, key) for key in ("beta", "gamma"))
    coeffs = [0, 1, 0, 1, beta, gamma]
    if any(value < 0 for value in coeffs):
        raise ValueError("only natural affine recurrence coefficients are supported")
    start = lean_state(need(p, "initial_state", list), "initial_state")
    state_claim = need(c, "state_at", dict)
    repeat_claim = need(c, "repeat_state", dict)
    reduction_claim = need(c, "index_reduction", dict)
    target_claim = need(c, "target_state", dict)
    conclusion = need(c, "conclusion", dict)
    cycle_start = need(state_claim, "step")
    repeat_index = need(repeat_claim, "step")
    period = need(c, "period")
    target_index = need(p, "target_index")
    require_equal(need(reduction_claim, "index"), target_index, "index_reduction.index")
    remainder = need(reduction_claim, "remainder")
    reduced_index = need(reduction_claim, "reduced")
    cycle_state = (need(state_claim, "x"), need(state_claim, "y"))
    repeated_state = (need(repeat_claim, "x"), need(repeat_claim, "y"))
    require_equal(need(target_claim, "step"), reduced_index, "target_state.step")
    target_state = (need(target_claim, "x"), need(target_claim, "y"))
    conclusion_state = lean_state(need(conclusion, "state", list), "conclusion.state")
    if not (0 <= cycle_start < repeat_index <= target_index):
        raise ValueError("invalid recurrence cycle indices")
    require_equal(period, repeat_index - cycle_start, "period")
    require_equal(remainder, (target_index - cycle_start) % period, "remainder")
    require_equal(reduced_index, cycle_start + remainder, "reduced_index")
    require_equal(cycle_state, state_at(p, cycle_start), "cycle_state")
    require_equal(repeated_state, state_at(p, repeat_index), "repeated_state")
    require_equal(repeated_state, cycle_state, "repeated state equality")
    if any(state_at(p, step) == cycle_state for step in range(cycle_start + 1, repeat_index)):
        raise ValueError("repeat_state is not the next occurrence of cycle_state")
    require_equal(target_state, state_at(p, reduced_index), "target_state")
    require_equal(conclusion_state, target_state, "conclusion.state")
    step_name = name + "_step"
    step_args = " ".join(n(value) for value in [modulus, *coeffs])
    start_lit = f"({n(start[0])}, {n(start[1])})"
    cycle_lit = f"({n(cycle_state[0])}, {n(cycle_state[1])})"
    target_lit = f"({n(target_state[0])}, {n(target_state[1])})"
    return (
        f"def {step_name} : ℕ × ℕ → ℕ × ℕ := affinePairStep {step_args}\n\n"
        f"theorem {name}_cycle_start : ({step_name}^[{n(cycle_start)}]) {start_lit} = "
        f"{cycle_lit} := by\n  native_decide\n\n"
        f"theorem {name}_repeat : ({step_name}^[{n(repeat_index)}]) {start_lit} = "
        f"{cycle_lit} := by\n  native_decide\n\n"
        f"theorem {name}_no_earlier_repeat : ∀ step ∈ Finset.Icc "
        f"{n(cycle_start + 1)} {n(repeat_index - 1)}, "
        f"({step_name}^[step]) {start_lit} ≠ {cycle_lit} := by\n"
        "  native_decide\n\n"
        f"theorem {name}_reduced_state : ({step_name}^[{n(reduced_index)}]) {start_lit} = "
        f"{target_lit} := by\n  native_decide\n\n"
        f"theorem {name} : ({step_name}^[{n(target_index)}]) {start_lit} = {target_lit} := by\n"
        f"  have hcycle : ({step_name}^[{n(period)}]) "
        f"(({step_name}^[{n(cycle_start)}]) {start_lit}) = "
        f"({step_name}^[{n(cycle_start)}]) {start_lit} := by\n"
        "    native_decide\n"
        f"  have hreduce := iterate_reduce_after_cycle {step_name} {start_lit} "
        f"(cycleStart := {n(cycle_start)}) (period := {n(period)}) "
        f"(offset := {n(target_index - cycle_start)}) hcycle\n"
        f"  have hleft : {n(cycle_start)} + ({n(target_index - cycle_start)} % {n(period)}) = "
        f"{n(reduced_index)} := by norm_num\n"
        f"  have hright : {n(cycle_start)} + {n(target_index - cycle_start)} = "
        f"{n(target_index)} := by norm_num\n"
        "  rw [hleft, hright] at hreduce\n"
        f"  exact hreduce.symm.trans {name}_reduced_state\n"
    )


BUILDERS = {
    "polynomial_value_obstruction": certificate_polynomial,
    "diophantine_solvability": certificate_diophantine,
    "modular_period_prime_filter": certificate_modular,
    "finite_double_count": certificate_double_count,
    "finite_recurrence_period": certificate_recurrence,
}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--results", type=Path, required=True)
    parser.add_argument("--private", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    results = read_jsonl(args.results)
    private_rows = {row["id"]: row for row in read_jsonl(args.private)}
    declarations: list[str] = []
    certified: list[str] = []
    skipped_parse_failures: list[str] = []
    skipped_non_strict: list[str] = []
    unsupported: list[dict[str, str]] = []
    families: dict[str, int] = {}
    for result in results:
        example_id = result["id"]
        parse_valid = result.get("parse_valid", result.get("parse_ok"))
        python_strict = result.get("python_strict")
        if not isinstance(parse_valid, bool):
            raise ValueError(f"result {example_id} lacks boolean parse_valid")
        if not isinstance(python_strict, bool):
            raise ValueError(f"result {example_id} lacks boolean python_strict")
        if not parse_valid:
            if python_strict:
                raise ValueError(f"result {example_id} is strict despite parse failure")
            skipped_parse_failures.append(example_id)
            continue
        if not python_strict:
            skipped_non_strict.append(example_id)
            continue
        if example_id not in private_rows:
            raise ValueError(f"missing private row for {example_id}")
        private = private_rows[example_id]
        family = result.get("family", private.get("family"))
        if family != private.get("family"):
            raise ValueError(f"family mismatch for {example_id}")
        if family not in SUPPORTED_FAMILIES:
            raise ValueError(f"unsupported family {family!r} for {example_id}")
        try:
            declaration = BUILDERS[family](
                theorem_name(example_id), instance_of(private), parsed_of(result)
            )
        except UnsupportedCertificate as exc:
            unsupported.append({"id": example_id, "family": family, "reason": str(exc)})
            continue
        except (KeyError, TypeError, ValueError, ZeroDivisionError) as exc:
            raise ValueError(f"cannot certify {example_id}: {exc}") from exc
        declarations.append(declaration)
        certified.append(example_id)
        families[family] = families.get(family, 0) + 1

    source = (
        "import VerifiedPlanHelpers\n\n"
        "namespace VerifiedPlanCertificates\n\n"
        "open Polynomial VerifiedPlanHelpers\n\n"
        + "\n\n".join(declarations)
        + "\n\nend VerifiedPlanCertificates\n"
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(source)
    helper_path = Path(__file__).resolve().parents[1] / "verifier" / "VerifiedPlanHelpers.lean"
    manifest = {
        "schema_version": 1,
        "contract": (
            "All deductions and witnesses are copied from typed model-plan claims. "
            "Private rows supply only concrete problem parameters. Python recomputation "
            "must pass before Lean source is emitted; no expected answer is substituted."
        ),
        "results": str(args.results),
        "results_sha256": sha256(args.results),
        "private": str(args.private),
        "private_sha256": sha256(args.private),
        "helper": str(helper_path),
        "helper_sha256": sha256(helper_path),
        "lean_compile": (
            "cd verifier && ~/.elan/bin/lake env lean -o "
            ".lake/build/lib/lean/VerifiedPlanHelpers.olean VerifiedPlanHelpers.lean "
            f"&& ~/.elan/bin/lake env lean -s 65536 {args.output.name}"
        ),
        "certified_ids": certified,
        "certified_by_family": families,
        "parse_failures_skipped": skipped_parse_failures,
        "non_strict_rows_skipped": skipped_non_strict,
        "unsupported_strict_rows": unsupported,
    }
    args.output.with_suffix(".manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
