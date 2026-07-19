#!/usr/bin/env python3
"""Build natural-language atomic-claim training and evaluation views."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


CONCEPTS = {
    "polynomial_value_obstruction": "congruence preservation for integer polynomials",
    "diophantine_solvability": "the greatest-common-divisor criterion for linear Diophantine equations",
}


def load_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def completion(row: dict) -> str:
    family, params = row["family"], row["parameters"]
    if family == "polynomial_value_obstruction":
        return (
            f"The input difference is {params['input_difference']}, and the proposed value difference "
            f"is {params['value_difference']}."
        )
    if family == "diophantine_solvability":
        relation = "does" if params["solvable"] else "does not"
        return f"The greatest common divisor is {params['gcd']}, and it {relation} divide {params['c']}."
    raise ValueError(family)


def task(family: str) -> str:
    if family == "polynomial_value_obstruction":
        return (
            "State exactly one sentence giving the signed input difference and the signed proposed "
            "value difference. Do not state a conclusion or any other claim."
        )
    return (
        "State exactly one sentence giving the greatest common divisor and whether it divides the "
        "right-hand side. Do not state a conclusion, witness, or any other claim."
    )


def build(split: str, data_dir: Path) -> list[dict]:
    prompts = {row["id"]: row for row in load_jsonl(data_dir / f"{split}.prompts.jsonl")}
    private = load_jsonl(data_dir / f"{split}.verifier.jsonl")
    rows = []
    for secret in private:
        family = secret["family"]
        if family not in CONCEPTS:
            continue
        statement = prompts[secret["id"]]["prompt"]
        prompt = (
            "Respond only in English.\n"
            f"Problem: {statement}\n"
            f"Relevant concept: {CONCEPTS[family]}.\n"
            f"Task: {task(family)}\n"
            "Claim: "
        )
        rows.append(
            {
                "id": secret["id"],
                "family": family,
                "prompt": prompt,
                "completion": completion(secret),
                "expected": completion(secret),
                "parameters": secret["parameters"],
                "split": split,
            }
        )
    return rows


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "".join(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n" for row in rows),
        encoding="utf-8",
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--data-dir", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()

    views = {split: build(split, args.data_dir) for split in ("train", "valid", "near", "paraphrase", "composition")}
    for split, rows in views.items():
        # Training files use only the fields consumed by the completion dataset.
        if split in {"train", "valid"}:
            write_jsonl(
                args.output_dir / "training" / f"{split}.jsonl",
                [{"prompt": row["prompt"], "completion": row["completion"], "metadata": {"id": row["id"], "family": row["family"]}} for row in rows],
            )
        write_jsonl(args.output_dir / f"{split}.prompts.jsonl", [{"id": row["id"], "family": row["family"], "prompt": row["prompt"]} for row in rows])
        write_jsonl(args.output_dir / f"{split}.verifier.jsonl", rows)
        if split not in {"train", "valid"}:
            no_concept = []
            wrong_concept = []
            for row in rows:
                concept_line = f"Relevant concept: {CONCEPTS[row['family']]}.\n"
                other_family = next(family for family in CONCEPTS if family != row["family"])
                no_concept.append({"id": row["id"], "family": row["family"], "prompt": row["prompt"].replace(concept_line, "")})
                wrong_concept.append({"id": row["id"], "family": row["family"], "prompt": row["prompt"].replace(concept_line, f"Relevant concept: {CONCEPTS[other_family]}.\n")})
            write_jsonl(args.output_dir / f"{split}.no_concept.prompts.jsonl", no_concept)
            write_jsonl(args.output_dir / f"{split}.wrong_concept.prompts.jsonl", wrong_concept)
    print(json.dumps({split: len(rows) for split, rows in views.items()}, sort_keys=True))


if __name__ == "__main__":
    main()
