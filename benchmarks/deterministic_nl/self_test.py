#!/usr/bin/env python3
"""End-to-end integrity and verifier tests for the deterministic benchmark."""

from __future__ import annotations

import json
import tempfile
from collections import Counter
from pathlib import Path

from benchmark import (
    ALL_FAMILIES,
    SHARED_FAMILIES,
    TEST_ONLY_FAMILIES,
    evaluate_response,
    generate_instances,
    oracle_response,
    validate_model_boundary,
)


def main() -> None:
    first = generate_instances()
    second = generate_instances()
    assert [instance.public() for instance in first] == [instance.public() for instance in second]
    assert [instance.private() for instance in first] == [instance.private() for instance in second]
    assert len({instance.id for instance in first}) == len(first)
    assert len({instance.prompt for instance in first}) == len(first)
    validate_model_boundary(first)

    dev_families = {instance.family for instance in first if instance.split == "dev"}
    test_families = {instance.family for instance in first if instance.split == "test"}
    assert dev_families == set(SHARED_FAMILIES)
    assert test_families == set(ALL_FAMILIES)
    assert not (set(TEST_ONLY_FAMILIES) & dev_families)

    # Shared-family test parameters occupy intentionally held-out ranges.
    for instance in first:
        if instance.split != "test":
            continue
        v = instance.verifier
        if instance.family == "integer_expression":
            assert all(value >= 21 for value in v["operands"])
        elif instance.family == "gcd_bezout":
            assert v["a"] // v["gcd"] >= 36 and v["b"] // v["gcd"] >= 36
        elif instance.family == "modular_inverse":
            assert v["modulus"] >= 81
        elif instance.family == "quadratic_integer_roots":
            assert all(abs(root) >= 10 for root in v["roots"])
        elif instance.family == "linear_system":
            assert all(abs(value) >= 7 for value in (v["a"], v["b"], v["c"], v["d"]))
            assert all(abs(value) >= 11 for value in (v["x"], v["y"]))

    oracle_results = [evaluate_response(instance, oracle_response(instance)) for instance in first]
    assert all(row["strict_pass"] for row in oracle_results)

    # Every family must reject a well-formed but deliberately wrong final answer.
    rejected = Counter()
    for instance in first:
        v = instance.verifier
        prefix = "I used a deliberate but incorrect calculation for this negative test. "
        if instance.family in {"integer_expression", "polynomial_remainder", "chinese_remainder"}:
            wrong = prefix + f"The answer is {v['answer'] + 1}."
        elif instance.family == "modular_inverse":
            wrong = prefix + f"The inverse is {v['inverse'] + 1}."
        elif instance.family == "quadratic_integer_roots":
            wrong = prefix + f"The integer roots are {v['roots'][0]} and {v['roots'][1] + 1}."
        elif instance.family == "linear_system":
            wrong = prefix + f"The solution is x = {v['x'] + 1} and y = {v['y']}."
        else:
            wrong = (
                prefix
                + f"The greatest common divisor is {v['gcd'] + 1}; coefficients x = {v['canonical_x']} "
                + f"and y = {v['canonical_y']} certify it."
            )
        result = evaluate_response(instance, wrong)
        if not result["strict_pass"]:
            rejected[instance.family] += 1
    assert set(rejected) == set(ALL_FAMILIES), rejected

    # Parser accepts alternative valid Bezout certificates, not only an oracle string.
    bezout = next(instance for instance in first if instance.family == "gcd_bezout")
    v = bezout.verifier
    shift = 3
    alt_x = v["canonical_x"] + shift * (v["b"] // v["gcd"])
    alt_y = v["canonical_y"] - shift * (v["a"] // v["gcd"])
    alternative = (
        "The Euclidean calculation supplies a different valid identity. "
        f"The greatest common divisor is {v['gcd']}; coefficients x = {alt_x} and y = {alt_y} certify it."
    )
    assert evaluate_response(bezout, alternative)["strict_pass"]

    # JSONL can round-trip model-facing Unicode and private metadata separately.
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "row.jsonl"
        path.write_text(json.dumps(first[0].public(), ensure_ascii=False) + "\n", encoding="utf-8")
        assert json.loads(path.read_text(encoding="utf-8"))["prompt"] == first[0].prompt

    print(
        json.dumps(
            {
                "status": "PASS",
                "instances": len(first),
                "oracle_strict_passes": len(oracle_results),
                "families": sorted(ALL_FAMILIES),
                "wrong_answer_rejections_by_family": dict(sorted(rejected.items())),
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
