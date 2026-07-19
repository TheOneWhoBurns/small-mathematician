#!/usr/bin/env python3
"""Audit and normalize candidate proof data without freezing a curriculum.

This script deliberately produces a *candidate pool*, not train/validation splits.
It removes fields that violate the small-model boundary, groups related examples,
and uses only sealed-evaluation statements to detect likely contamination.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[1]
PROCESSED = ROOT / "assets" / "data" / "processed"
INPUTS = PROCESSED / "candidates"
EVAL = PROCESSED / "eval"
OUTPUT = PROCESSED / "audited"

ALLOWED_FINEPROOF_CATEGORIES = {
    "Algebra",
    "Calculus",
    "Combinatorics",
    "Geometry",
    "Inequalities",
    "Logic/Puzzles",
    "Number Theory",
    "Other",
}

WIKI_LINK = re.compile(r"\[\[([^\]|]+)\|([^\]]+)\]\]")
WIKI_LINK_SIMPLE = re.compile(r"\[\[([^\]]+)\]\]")
WIKI_QED = re.compile(r"\{\{\s*qed\s*\}\}", re.IGNORECASE)
WIKI_EQN_BOUNDARY = re.compile(r"\{\{\s*(?:begin|end)-eqn\s*\}\}", re.IGNORECASE)
LATEX_LABEL = re.compile(r"\\label\{[^{}]*\}")
COMMENT = re.compile(r"(?m)%[^\n]*")
SPACE = re.compile(r"[ \t]+")
BLANKS = re.compile(r"\n{3,}")
TOKEN = re.compile(r"[a-z]+|\d+(?:\.\d+)?|<=|>=|!=|[=<>+*/^-]")
NUMBER = re.compile(r"\b\d+(?:\.\d+)?\b")


def read_jsonl(path: Path) -> Iterable[dict[str, Any]]:
    with path.open(encoding="utf-8") as handle:
        for line in handle:
            if line.strip():
                yield json.loads(line)


def write_jsonl(path: Path, rows: Iterable[dict[str, Any]]) -> int:
    path.parent.mkdir(parents=True, exist_ok=True)
    count = 0
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
            count += 1
    return count


def sha(text: str, length: int = 20) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()[:length]


def clean_text(text: str, *, proofwiki: bool = False) -> tuple[str, list[str]]:
    flags: list[str] = []
    text = text.replace("\r\n", "\n").replace("\r", "\n")
    if proofwiki:
        text = WIKI_LINK.sub(lambda match: match.group(2), text)
        text = WIKI_LINK_SIMPLE.sub(lambda match: match.group(1), text)
        text = WIKI_QED.sub("QED.", text)
        text = WIKI_EQN_BOUNDARY.sub("", text)
        if "{{" in text or "}}" in text:
            flags.append("unresolved_proofwiki_template")
    text = LATEX_LABEL.sub("", text)
    text = COMMENT.sub("", text)
    text = "\n".join(SPACE.sub(" ", line).strip().lstrip(":").strip() for line in text.splitlines())
    text = BLANKS.sub("\n\n", text).strip()
    if re.search(r"\\(?:ref|eqref)\{", text):
        flags.append("unresolved_cross_reference")
    if re.search(r"\\begin\{(?:alist|enumerate|itemize)\}", text):
        flags.append("list_markup")
    if not text:
        flags.append("empty_text")
    return text, flags


def normalized(text: str, *, mask_numbers: bool = False) -> str:
    text = text.lower()
    text = WIKI_LINK.sub(lambda match: match.group(2), text)
    text = WIKI_LINK_SIMPLE.sub(lambda match: match.group(1), text)
    text = re.sub(r"\\(?:left|right|displaystyle|textstyle|mathrm|mathbf|operatorname)", "", text)
    text = re.sub(r"[^a-z0-9=<>+*/^.-]+", " ", text)
    if mask_numbers:
        text = NUMBER.sub("#", text)
    return " ".join(text.split())


def tokens(text: str) -> list[str]:
    return TOKEN.findall(normalized(text))


def shingles(text: str, width: int = 5) -> set[tuple[str, ...]]:
    values = tokens(text)
    if not values:
        return set()
    if len(values) < width:
        return {tuple(values)}
    return {tuple(values[index : index + width]) for index in range(len(values) - width + 1)}


def word_count(text: str) -> int:
    return len(re.findall(r"\b\w+\b", text))


def percentile(values: list[int], quantile: float) -> int | None:
    if not values:
        return None
    ordered = sorted(values)
    index = min(len(ordered) - 1, math.floor(quantile * (len(ordered) - 1)))
    return ordered[index]


def valid_seed_label(value: Any) -> str | None:
    if not isinstance(value, str):
        return None
    value = " ".join(value.split()).strip(" -")
    if not (2 <= len(value) <= 80) or len(value.split()) > 8:
        return None
    if any(marker in value.lower() for marker in ("classification", "the problem", "we need", "therefore")):
        return None
    return value


def load_eval_statements() -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for path in sorted(EVAL.glob("*.jsonl")):
        for row in read_jsonl(path):
            rows.append({"id": f"{path.stem}:{row['id']}", "statement": row["statement"]})
    return rows


class EvalOverlapIndex:
    def __init__(self, rows: list[dict[str, str]]) -> None:
        self.rows = rows
        self.sets = [shingles(row["statement"]) for row in rows]
        self.exact: dict[str, list[int]] = defaultdict(list)
        self.inverted: dict[tuple[str, ...], list[int]] = defaultdict(list)
        for index, row in enumerate(rows):
            self.exact[normalized(row["statement"])].append(index)
            for gram in self.sets[index]:
                self.inverted[gram].append(index)

    def query(self, statement: str) -> dict[str, Any]:
        exact = self.exact.get(normalized(statement), [])
        if exact:
            index = exact[0]
            return {"eval_id": self.rows[index]["id"], "jaccard_5gram": 1.0, "exact": True}
        query_set = shingles(statement)
        candidates: Counter[int] = Counter()
        for gram in query_set:
            candidates.update(self.inverted.get(gram, []))
        best_index: int | None = None
        best_score = 0.0
        # Shared-gram count is an upper-bound-friendly prefilter. Evaluate the
        # strongest 24 candidates exactly; the eval collection is sealed and small.
        for index, _shared in candidates.most_common(24):
            other = self.sets[index]
            union = len(query_set | other)
            score = len(query_set & other) / union if union else 0.0
            if score > best_score:
                best_index, best_score = index, score
        return {
            "eval_id": self.rows[best_index]["id"] if best_index is not None else None,
            "jaccard_5gram": round(best_score, 6),
            "exact": False,
        }


def source_name(row: dict[str, Any]) -> str:
    return (
        row.get("metadata", {}).get("dataset")
        or row.get("provenance", {}).get("dataset")
        or "unknown"
    )


def candidate_rows() -> Iterable[dict[str, Any]]:
    for row in read_jsonl(INPUTS / "fineproofs.jsonl"):
        category = valid_seed_label((row.get("concept_labels") or [None])[0])
        labels = [category] if category in ALLOWED_FINEPROOF_CATEGORIES else []
        yield {
            "id": row["id"],
            "statement": row.get("statement") or "",
            "target_argument": row.get("argument") or "",
            "seed_concept_labels": labels,
            "metadata": {
                **row.get("provenance", {}),
                "teacher_grade": row.get("quality", {}).get("teacher_grade"),
                "difficulty_reward": row.get("quality", {}).get("difficulty_reward"),
                "raw_category": (row.get("concept_labels") or [None])[0],
                "reasoning_trace_removed": True,
            },
        }
    for row in read_jsonl(INPUTS / "naturalproofs.jsonl"):
        labels = [label for value in row.get("concept_labels") or [] if (label := valid_seed_label(value))]
        yield {
            "id": row["id"],
            "statement": row.get("statement") or "",
            "target_argument": row.get("argument") or "",
            "seed_concept_labels": labels,
            "metadata": {
                **row.get("provenance", {}),
                "title": row.get("title"),
                "statement_references": row.get("statement_references") or [],
                "argument_references": row.get("argument_references") or [],
            },
        }


def audit_row(row: dict[str, Any], overlap: EvalOverlapIndex) -> dict[str, Any]:
    metadata = row["metadata"]
    domain = metadata.get("domain")
    proofwiki = domain == "proofwiki"
    statement, statement_flags = clean_text(row["statement"], proofwiki=proofwiki)
    argument, argument_flags = clean_text(row["target_argument"], proofwiki=proofwiki)
    flags = sorted(set(statement_flags + argument_flags))
    statement_words = word_count(statement)
    argument_words = word_count(argument)
    if statement_words < 5:
        flags.append("statement_too_short")
    if statement_words > 900:
        flags.append("statement_too_long")
    if argument_words < 12:
        flags.append("argument_too_short")
    if argument_words > 2500:
        flags.append("argument_too_long")
    if source_name(row) == "lm-provers/FineProofs-SFT":
        if metadata.get("teacher_grade") != 7:
            flags.append("teacher_grade_below_7")
        if not row["seed_concept_labels"]:
            flags.append("invalid_or_missing_category")

    family_basis = normalized(statement, mask_numbers=True)
    title = metadata.get("title")
    if title and domain in {"proofwiki", "trench"}:
        family_basis = f"title:{normalized(title, mask_numbers=True)}"
    eval_overlap = overlap.query(statement)
    if eval_overlap["exact"]:
        flags.append("exact_eval_overlap")
    elif eval_overlap["jaccard_5gram"] >= 0.70:
        flags.append("probable_eval_overlap")

    hard_flags = {
        "empty_text",
        "statement_too_short",
        "statement_too_long",
        "argument_too_short",
        "argument_too_long",
        "unresolved_proofwiki_template",
        "exact_eval_overlap",
        "probable_eval_overlap",
    }
    eligible_default = not bool(hard_flags.intersection(flags))
    if source_name(row) == "lm-provers/FineProofs-SFT":
        eligible_default = eligible_default and metadata.get("teacher_grade") == 7 and bool(row["seed_concept_labels"])

    return {
        "id": row["id"],
        "statement": statement,
        "target_argument": argument,
        "seed_concept_labels": row["seed_concept_labels"],
        "family_id": f"family-{sha(family_basis)}",
        "content_id": f"content-{sha(normalized(statement) + chr(0) + normalized(argument))}",
        "quality": {
            "eligible_default": eligible_default,
            "flags": sorted(set(flags)),
            "statement_words": statement_words,
            "argument_words": argument_words,
            "sealed_eval_overlap": eval_overlap,
        },
        "metadata": metadata,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()

    eval_rows = load_eval_statements()
    overlap = EvalOverlapIndex(eval_rows)
    rows = [audit_row(row, overlap) for row in candidate_rows()]

    duplicate_ids: dict[str, list[str]] = defaultdict(list)
    unique_rows: list[dict[str, Any]] = []
    seen: set[str] = set()
    for row in rows:
        duplicate_ids[row["content_id"]].append(row["id"])
        if row["content_id"] not in seen:
            unique_rows.append(row)
            seen.add(row["content_id"])

    duplicates = [
        {"content_id": content_id, "ids": ids, "count": len(ids)}
        for content_id, ids in sorted(duplicate_ids.items())
        if len(ids) > 1
    ]
    eligible = [row for row in unique_rows if row["quality"]["eligible_default"]]

    source_counts = Counter(source_name(row) for row in unique_rows)
    domain_counts = Counter(row["metadata"].get("domain", "fineproofs") for row in unique_rows)
    flag_counts = Counter(flag for row in unique_rows for flag in row["quality"]["flags"])
    family_counts = Counter(row["family_id"] for row in unique_rows)
    statement_lengths = [row["quality"]["statement_words"] for row in unique_rows]
    argument_lengths = [row["quality"]["argument_words"] for row in unique_rows]
    report = {
        "schema_version": 1,
        "purpose": "audited candidate pool; not a frozen curriculum or split",
        "natural_language_boundary": {
            "reasoning_trace_removed": True,
            "lean_fields_present": False,
            "eval_solutions_used_for_overlap": False,
        },
        "counts": {
            "input": len(rows),
            "unique_content": len(unique_rows),
            "default_eligible": len(eligible),
            "duplicate_groups": len(duplicates),
            "families": len(family_counts),
            "multi_example_families": sum(count > 1 for count in family_counts.values()),
            "sealed_eval_statements": len(eval_rows),
        },
        "by_source": dict(sorted(source_counts.items())),
        "by_domain": dict(sorted(domain_counts.items())),
        "quality_flags": dict(sorted(flag_counts.items())),
        "lengths_words": {
            "statement": {"p50": percentile(statement_lengths, 0.5), "p90": percentile(statement_lengths, 0.9), "max": max(statement_lengths)},
            "argument": {"p50": percentile(argument_lengths, 0.5), "p90": percentile(argument_lengths, 0.9), "max": max(argument_lengths)},
        },
        "non_decisions": [
            "No mathematical domain was selected.",
            "No train, validation, or curriculum split was frozen.",
            "Quality thresholds remain versioned hypotheses and may be changed by measured experiments.",
        ],
    }

    args.output.mkdir(parents=True, exist_ok=True)
    write_jsonl(args.output / "pool.jsonl", unique_rows)
    write_jsonl(args.output / "eligible-default.jsonl", eligible)
    write_jsonl(args.output / "duplicate-groups.jsonl", duplicates)
    (args.output / "audit-report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
