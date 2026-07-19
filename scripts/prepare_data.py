#!/usr/bin/env python3
"""Create natural-language-only views and keep formal verifier data isolated."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Iterable

import pyarrow.parquet as pq


ROOT = Path(__file__).resolve().parents[1]
RAW = ROOT / "assets" / "data" / "raw"
PROCESSED = ROOT / "assets" / "data" / "processed"


def write_jsonl(path: Path, rows: Iterable[dict[str, Any]]) -> int:
    path.parent.mkdir(parents=True, exist_ok=True)
    count = 0
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False) + "\n")
            count += 1
    return count


def parquet_rows(paths: list[Path]) -> Iterable[dict[str, Any]]:
    for path in paths:
        yield from pq.read_table(path).to_pylist()


def fineproof_rows() -> Iterable[dict[str, Any]]:
    paths = sorted((RAW / "fineproofs" / "data").glob("*.parquet"))
    for index, row in enumerate(parquet_rows(paths)):
        yield {
            "id": f"fineproofs-{index:05d}",
            "statement": row["problem"],
            "reasoning_trace": row["reasoning_content"],
            "argument": row["proof"],
            "concept_labels": [row["category"]] if row.get("category") else [],
            "quality": {
                "teacher_grade": row.get("gemini-3-pro-grade"),
                "difficulty_reward": row.get("qwen3-4b-thinking-reward@128"),
            },
            "provenance": {
                "dataset": "lm-provers/FineProofs-SFT",
                "competition": row.get("competition"),
                "source": row.get("source"),
            },
        }


def naturalproof_rows() -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    definitions: list[dict[str, Any]] = []
    theorems: list[dict[str, Any]] = []
    for path in sorted((RAW / "naturalproofs").glob("*.json")):
        payload = json.loads(path.read_text())
        dataset_name = path.stem.removeprefix("naturalproofs_")
        dataset = payload["dataset"]
        for item in dataset.get("definitions", []):
            record = {
                "id": f"naturalproofs:{dataset_name}:{item.get('id')}",
                "title": item.get("title"),
                "statement": "\n".join(item.get("contents") or []),
                "concept_labels": item.get("categories") or [],
                "references": item.get("refs") or [],
                "provenance": {"dataset": "NaturalProofs 2.0.0", "domain": dataset_name},
            }
            definitions.append(record)
        for item in dataset.get("theorems", []):
            statement = "\n".join(item.get("contents") or [])
            shared = {
                "title": item.get("title"),
                "statement": statement,
                "concept_labels": item.get("categories") or [],
                "statement_references": item.get("refs") or [],
                "provenance": {"dataset": "NaturalProofs 2.0.0", "domain": dataset_name},
            }
            for proof_index, proof in enumerate(item.get("proofs") or []):
                theorems.append(
                    {
                        "id": f"naturalproofs:{dataset_name}:{item.get('id')}:proof-{proof_index}",
                        **shared,
                        "argument": "\n".join(proof.get("contents") or []),
                        "argument_references": proof.get("refs") or [],
                    }
                )
    return definitions, theorems


def proofbench_rows() -> Iterable[dict[str, Any]]:
    path = RAW / "proofbench" / "data" / "all-00000-of-00001.parquet"
    for row in parquet_rows([path]):
        yield {
            "id": row["problem_id"],
            "statement": row["problem"],
            "reference_argument": row["solution"],
            "grading_scheme": row["grading_scheme"],
            "provenance": {"dataset": "lm-provers/ProofBench"},
        }


def ma_proofbench_rows() -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    natural: list[dict[str, Any]] = []
    formal: list[dict[str, Any]] = []
    path = RAW / "ma-proofbench" / "ma_proofbench.jsonl"
    for index, line in enumerate(path.read_text().splitlines()):
        row = json.loads(line)
        record_id = row.get("id") or row.get("name") or f"ma-proofbench-{index:03d}"
        natural.append(
            {
                "id": record_id,
                "statement": row["informal_statement"],
                "concept_labels": [value for value in (row.get("topic"), row.get("tag")) if value],
                "difficulty": row.get("split"),
                "provenance": {"dataset": "openbmb/MA-ProofBench"},
            }
        )
        formal.append(
            {
                "id": record_id,
                "formal_statement": row["formal_statement"],
                "header": row.get("header"),
                "lean_version": row.get("version"),
            }
        )
    return natural, formal


def main() -> None:
    counts: dict[str, int] = {}
    counts["fineproofs_candidates"] = write_jsonl(
        PROCESSED / "candidates" / "fineproofs.jsonl", fineproof_rows()
    )
    definitions, theorems = naturalproof_rows()
    counts["naturalproofs_definitions"] = write_jsonl(
        PROCESSED / "knowledge" / "definitions.jsonl", definitions
    )
    counts["naturalproofs_theorems"] = write_jsonl(
        PROCESSED / "candidates" / "naturalproofs.jsonl", theorems
    )
    counts["proofbench_eval"] = write_jsonl(
        PROCESSED / "eval" / "proofbench.jsonl", proofbench_rows()
    )
    ma_natural, ma_formal = ma_proofbench_rows()
    counts["ma_proofbench_eval"] = write_jsonl(
        PROCESSED / "eval" / "ma-proofbench-natural.jsonl", ma_natural
    )
    counts["ma_proofbench_formal"] = write_jsonl(
        PROCESSED / "verifier-only" / "ma-proofbench-lean.jsonl", ma_formal
    )
    (PROCESSED / "counts.json").write_text(json.dumps(counts, indent=2) + "\n")
    for name, count in counts.items():
        print(f"{name}: {count}")


if __name__ == "__main__":
    main()
