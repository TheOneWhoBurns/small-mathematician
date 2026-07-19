#!/usr/bin/env python3
"""Dispatch natural-language problems to fixed mathematical executors.

The execution output is sealed before private verifier facts are opened.
Only the model's predicted route and the public natural-language statement are
available to the executor.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
from pathlib import Path


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def integer_list(values: list[int]) -> str:
    return ", ".join(map(str, values)) if values else "none"


def extended_gcd(a: int, b: int) -> tuple[int, int, int]:
    old_r, r, old_s, s, old_t, t = a, b, 1, 0, 0, 1
    while r:
        quotient = old_r // r
        old_r, r = r, old_r - quotient * r
        old_s, s = s, old_s - quotient * s
        old_t, t = t, old_t - quotient * t
    if old_r < 0:
        return -old_r, -old_s, -old_t
    return old_r, old_s, old_t


def is_prime(value: int) -> bool:
    return value >= 2 and all(value % divisor for divisor in range(2, math.isqrt(value) + 1))


def execute_polynomial(prompt: str) -> str:
    match = re.search(r"P\((-?\d+)\) = (-?\d+) and P\((-?\d+)\) = (-?\d+)", prompt)
    if not match:
        raise ValueError("polynomial parser rejected statement")
    u, a_value, v, b_value = map(int, match.groups())
    input_difference = v - u
    value_difference = b_value - a_value
    modulus = abs(input_difference)
    remainder = value_difference % modulus
    facts = [
        f"The input difference is {input_difference}.",
        f"The proposed value difference is {value_difference}.",
        "Every integer-coefficient polynomial makes the input difference divide the value difference.",
        f"The proposed value difference leaves remainder {remainder} modulo {modulus}.",
    ]
    if remainder == 0:
        facts.append(f"The quotient is {value_difference // input_difference}.")
        facts.append("Such an integer-coefficient polynomial can exist.")
    else:
        facts.append("Such an integer-coefficient polynomial cannot exist.")
    return " ".join(facts)


def execute_diophantine(prompt: str) -> str:
    match = re.search(r"whether (-?\d+)x \+ (-?\d+)y = (-?\d+) has an integer solution", prompt)
    if not match:
        raise ValueError("Diophantine parser rejected statement")
    a, b, c = map(int, match.groups())
    gcd, u, v = extended_gcd(a, b)
    solvable = c % gcd == 0
    facts = [
        f"The greatest common divisor is {gcd}.",
        f"It {'does' if solvable else 'does not'} divide {c}.",
    ]
    if solvable:
        scale = c // gcd
        facts.extend(
            [
                f"Bezout coefficients are {u} and {v}.",
                f"A solution is x = {u * scale} and y = {v * scale}.",
                "An integer solution exists.",
            ]
        )
    else:
        facts.extend(
            [
                f"Every integer combination of {a} and {b} is divisible by {gcd}.",
                "No integer solution exists.",
            ]
        )
    return " ".join(facts)


def execute_modular(prompt: str) -> str:
    match = re.search(
        r"For powers of (\d+) modulo (\d+), find all prime exponents from (\d+) through (\d+) that give residue (\d+)",
        prompt,
    )
    if not match:
        raise ValueError("modular parser rejected statement")
    base, modulus, low, high, target = map(int, match.groups())
    value = 1
    period = None
    for candidate in range(1, modulus * modulus + 1):
        value = value * base % modulus
        if value == 1:
            period = candidate
            break
    if period is None:
        raise ValueError("no multiplicative period")
    classes = [exponent for exponent in range(period) if pow(base, exponent, modulus) == target]
    primes = [value for value in range(low, high + 1) if is_prime(value)]
    valid = [value for value in primes if value % period in classes]
    return " ".join(
        [
            f"The powers of {base} repeat with period {period} modulo {modulus}.",
            f"The target residue occurs for exponent classes {integer_list(classes)} modulo {period}.",
            f"The prime candidates in the stated range are {integer_list(primes)}.",
            f"After intersecting the conditions, the valid exponents are {integer_list(valid)}.",
            f"The required exponents are {integer_list(valid)}.",
        ]
    )


def execute_double_count(prompt: str) -> str:
    match = re.search(
        r"ordered (\d+)-tuples of subsets of the (\d+)-element universe numbered from (-?\d+) through (-?\d+)\. Class 1 has (\d+) elements of weight (-?\d+), and class 2 has (\d+) elements of weight (-?\d+)",
        prompt,
    )
    if not match:
        raise ValueError("double-count parser rejected statement")
    length, universe, _start, _end, size1, weight1, size2, weight2 = map(int, match.groups())
    total = 2 ** (universe * length)
    absent = 2 ** (length * (universe - 1))
    contain = total - absent
    contribution1 = size1 * weight1 * contain
    contribution2 = size2 * weight2 * contain
    answer = contribution1 + contribution2
    return " ".join(
        [
            f"There are {total} ordered tuples in total.",
            f"A fixed element is absent from {absent} tuples.",
            f"So a fixed element occurs in {contain} tuples.",
            f"Class 1 has {size1} elements of weight {weight1}, contributing {contribution1}.",
            f"Class 2 has {size2} elements of weight {weight2}, contributing {contribution2}.",
            f"The weighted sum of the union sizes is {answer}.",
        ]
    )


def execute_recurrence(prompt: str) -> str:
    match = re.search(
        r"recurrence modulo (\d+) starts at \((-?\d+), (-?\d+)\).*next state is \(y, x \+ (-?\d+)y \+ (-?\d+)\).*step (\d+)",
        prompt,
    )
    if not match:
        raise ValueError("recurrence parser rejected statement")
    modulus, x0, y0, beta, gamma, target_index = map(int, match.groups())
    state = (x0 % modulus, y0 % modulus)
    states: list[tuple[int, int]] = []
    seen: dict[tuple[int, int], int] = {}
    while state not in seen:
        seen[state] = len(states)
        states.append(state)
        state = (state[1], (state[0] + beta * state[1] + gamma) % modulus)
    cycle_start = seen[state]
    repeat_step = len(states)
    period = repeat_step - cycle_start
    remainder = (target_index - cycle_start) % period
    reduced = cycle_start + remainder
    target = states[reduced]
    cycle_state = states[cycle_start]
    return " ".join(
        [
            f"The state at step {cycle_start} is ({cycle_state[0]}, {cycle_state[1]}).",
            f"The same state next appears at step {repeat_step}.",
            f"Thus the cycle has period {period}.",
            f"Index {target_index} reduces to step {reduced} because the cycle remainder is {remainder}.",
            f"The state there is ({target[0]}, {target[1]}).",
            f"The required state is ({target[0]}, {target[1]}).",
        ]
    )


EXECUTORS = {
    "polynomial_value_obstruction": execute_polynomial,
    "diophantine_solvability": execute_diophantine,
    "modular_period_prime_filter": execute_modular,
    "finite_double_count": execute_double_count,
    "finite_recurrence_period": execute_recurrence,
}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--prompts", type=Path, required=True)
    parser.add_argument("--route-predictions", type=Path, required=True)
    parser.add_argument("--private", type=Path, required=True)
    parser.add_argument("--targets", type=Path, required=True)
    parser.add_argument("--responses", type=Path, required=True)
    parser.add_argument("--seal", type=Path, required=True)
    parser.add_argument("--details", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()

    prompts = read_jsonl(args.prompts)
    predictions = {row["id"]: row for row in read_jsonl(args.route_predictions)}
    if {row["id"] for row in prompts} != predictions.keys():
        raise ValueError("prompt and route-prediction IDs differ")
    responses = []
    route_parse_failures = []
    for row in prompts:
        route = predictions[row["id"]]["predicted_route"]
        try:
            response = EXECUTORS[route](row["prompt"])
        except ValueError as error:
            response = ""
            route_parse_failures.append({"id": row["id"], "predicted_route": route, "error": str(error)})
        responses.append({"id": row["id"], "predicted_route": route, "response": response})
    args.responses.parent.mkdir(parents=True, exist_ok=True)
    with args.responses.open("w", encoding="utf-8") as handle:
        for row in responses:
            handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
    seal = {
        "schema_version": 1,
        "contract": "responses generated from public natural-language prompts and predicted routes before private verifier data was opened",
        "prompts": str(args.prompts),
        "prompts_sha256": digest(args.prompts),
        "route_predictions": str(args.route_predictions),
        "route_predictions_sha256": digest(args.route_predictions),
        "responses": str(args.responses),
        "responses_sha256": digest(args.responses),
        "count": len(responses),
        "route_parse_failures": route_parse_failures,
        "private_opened": False,
    }
    args.seal.write_text(json.dumps(seal, indent=2, sort_keys=True) + "\n")

    # Private facts are opened only after the response file is sealed.
    import sys
    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "benchmarks" / "verified_plan_ladder"))
    from benchmark import Instance, evaluate_response

    private = {row["id"]: row for row in read_jsonl(args.private)}
    targets = {row["id"]: row for row in read_jsonl(args.targets)}
    details = []
    for public, generated in zip(prompts, responses, strict=True):
        verifier = private[public["id"]]
        target = targets[public["id"]]
        instance = Instance(
            id=public["id"], family=verifier["family"], split=verifier["split"],
            semantic_instance_id=verifier["semantic_instance_id"], parameter_hash=verifier["parameter_hash"],
            graph_id=verifier["graph_id"], prompt_template_id=verifier["prompt_template_id"],
            prompt=public["prompt"], target_free=target["target_free"], target_ordered=target["target_ordered"],
            parameters=verifier["parameters"], required_facts=verifier["required_facts"], conclusion=verifier["conclusion"],
        )
        details.append(evaluate_response(instance, generated["response"], "ordered"))
    with args.details.open("w", encoding="utf-8") as handle:
        for row in details:
            handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
    report = {
        "schema_version": 1,
        "count": len(details),
        "route_parse_failures": len(route_parse_failures),
        "strict": sum(row["python_strict"] for row in details),
        "strict_rate": sum(row["python_strict"] for row in details) / len(details),
        "private_math_valid": sum(row["private_math_valid"] for row in details),
        "responses_sha256": digest(args.responses),
        "seal_sha256": digest(args.seal),
        "details_sha256": digest(args.details),
        "private_sha256": digest(args.private),
        "targets_sha256": digest(args.targets),
    }
    args.report.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
