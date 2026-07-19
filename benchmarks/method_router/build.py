#!/usr/bin/env python3
"""Build a hint-reduced natural-language mathematical-method routing benchmark."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path


METHODS = {
    "polynomial_value_obstruction": (
        "Use congruence preservation for integer polynomials: compare the input "
        "difference with the value difference."
    ),
    "diophantine_solvability": (
        "Use the greatest-common-divisor criterion for linear Diophantine "
        "equations, with a Bezout witness when a solution exists."
    ),
    "modular_period_prime_filter": (
        "Use periodicity of modular powers: find the exponent cycle and inspect "
        "the relevant residue classes."
    ),
    "finite_double_count": (
        "Use double counting of element incidences: count how often one fixed "
        "element appears, then sum over the universe."
    ),
    "finite_recurrence_period": (
        "Use cycle detection for finite recurrences: find a repeated state and "
        "reduce the requested index modulo the cycle length."
    ),
}

MARKERS = {
    "polynomial_value_obstruction": "congruence preservation for integer polynomials",
    "diophantine_solvability": "greatest-common-divisor criterion for linear diophantine equations",
    "modular_period_prime_filter": "periodicity of modular powers",
    "finite_double_count": "double counting of element incidences",
    "finite_recurrence_period": "cycle detection for finite recurrences",
}


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def hint_reduced(prompt: str, family: str) -> str:
    text = prompt.strip()
    if family in {"polynomial_value_obstruction", "diophantine_solvability"}:
        if "?" in text:
            question = text.split("?", 1)[0].strip() + "?"
        else:
            question = text.split(".", 1)[0].strip() + "."
        question = re.sub(
            r"^Starting from the divisibility condition and working toward a witness,\s*",
            "",
            question,
            flags=re.IGNORECASE,
        )
    elif family == "modular_period_prime_filter":
        question = text.split("?", 1)[0].strip() + "?"
    elif family == "finite_double_count":
        question = re.sub(
            r"\s+by (?:double counting element incidences|combining complement counting and the two class contributions),?",
            "",
            text,
            flags=re.IGNORECASE,
        )
        question = re.sub(
            r"\s+Compute the total by counting one fixed point first,?",
            " Compute the total.",
            question,
            flags=re.IGNORECASE,
        )
        question = re.sub(r"\s+and explain (?:it|the argument) in ordinary English\.?", "", question, flags=re.IGNORECASE)
    elif family == "finite_recurrence_period":
        question = re.sub(
            r"\s+by identifying a repeated state and reducing the index",
            "",
            text,
            flags=re.IGNORECASE,
        )
        question = re.sub(
            r"\s+using a repeated state",
            "",
            question,
            flags=re.IGNORECASE,
        )
        question = re.sub(r"\s+Give a checkable English plan\.?", "", question, flags=re.IGNORECASE)
        question = re.sub(r",?\s+and explain the reduction in English\.?", ".", question, flags=re.IGNORECASE)
    else:
        raise ValueError(f"unknown family {family}")
    question = re.sub(r"\.\?", ".", question.strip())
    return (
        question
        + " State the single most useful mathematical idea or method in ordinary English. "
        + "Do not calculate the final answer."
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-data", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    args.output.mkdir(parents=True, exist_ok=True)
    counts: dict[str, int] = {}
    source_hashes: dict[str, str] = {}
    for split in ("train", "valid", "train_fit", "near", "paraphrase", "composition"):
        source = args.source_data / f"{split}.prompts.jsonl"
        source_rows = read_jsonl(source)
        prompt_rows: list[dict] = []
        completion_rows: list[dict] = []
        for row in source_rows:
            family = row["family"]
            prompt = hint_reduced(row["prompt"], family)
            prompt_rows.append({"id": row["id"], "family": family, "prompt": prompt})
            completion_rows.append(
                {
                    "prompt": "Respond only in English.\n" + prompt + "\nMethod:\n",
                    "completion": METHODS[family],
                    "metadata": {"id": row["id"], "family": family},
                }
            )
        prompt_path = args.output / f"{split}.prompts.jsonl"
        with prompt_path.open("w", encoding="utf-8") as handle:
            for row in prompt_rows:
                handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
        if split in {"train", "valid"}:
            completion_path = args.output / f"{split}.jsonl"
            with completion_path.open("w", encoding="utf-8") as handle:
                for row in completion_rows:
                    handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
        all_completion_path = args.output / f"{split}.completions.jsonl"
        with all_completion_path.open("w", encoding="utf-8") as handle:
            for row in completion_rows:
                handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
        counts[split] = len(source_rows)
        source_hashes[split] = sha256(source)

    manifest = {
        "schema_version": 1,
        "purpose": "method selection only; not proof generation",
        "input_contract": "hint-reduced ordinary-English mathematical statement",
        "output_contract": "one ordinary-English mathematical method",
        "executor_contract": "a fixed family executor may instantiate arithmetic only after method selection",
        "methods": METHODS,
        "markers": MARKERS,
        "counts": counts,
        "source_sha256": source_hashes,
    }
    (args.output / "manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
