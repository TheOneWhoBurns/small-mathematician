#!/usr/bin/env python3
"""Validate v2 balance, matching, semantics, and lexical separation from v1."""

from __future__ import annotations

import hashlib
import json
import re
import tempfile
from collections import Counter, defaultdict
from pathlib import Path

from generate import (
    DATA,
    DECOYS,
    FORBIDDEN_GOLD_PHRASES,
    RELATION_AUDIT_TERMS,
    ROUTES,
    V1_DISTINCTIVE_RELATION_PHRASES,
    build,
    generate_rows,
)


V1_PROMPTS = Path(__file__).resolve().parents[1] / "contrast" / "data" / "prompts.jsonl"
NGRAM_SIZE = 8


def _read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def _normalized_tokens(text: str) -> list[str]:
    return re.findall(r"[a-z]+|<num>", re.sub(r"[+-]?\d+", " <num> ", text.lower()))


def _ngrams(text: str, size: int = NGRAM_SIZE) -> set[tuple[str, ...]]:
    tokens = _normalized_tokens(text)
    return {tuple(tokens[index:index + size]) for index in range(len(tokens) - size + 1)}


def _words(text: str) -> list[str]:
    return re.findall(r"\b[\w'-]+\b", text)


def _numbers(text: str) -> list[str]:
    return re.findall(r"(?<![A-Za-z_])[+-]?\d+(?![A-Za-z_])", text)


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _relation_is_unambiguous(row: dict) -> bool:
    prompt = str(row["prompt"]).lower()
    route = str(row["route"])
    if not all(term in prompt for term in RELATION_AUDIT_TERMS[route]):
        return False
    values = list(map(int, _numbers(prompt)))
    if len(values) != 6:
        return False
    a, b, c, d, e, f = values
    # Route-specific mathematical well-formedness checks independent of labels.
    if route == "polynomial_value_obstruction":
        return a != b
    if route == "diophantine_solvability":
        return a > 0 and b > 0
    if route == "modular_period_prime_filter":
        return 1 < a < b and 0 <= c < b and d <= e
    if route == "finite_double_count":
        return a > 0 and b > 0
    return e > 1 and f > e and all(value >= 0 for value in (a, b, c, d))


def main() -> None:
    first, second = generate_rows(), generate_rows()
    assert first == second
    assert len(first) == 100 and len({row["id"] for row in first}) == 100
    assert len({row["prompt"] for row in first}) == 100
    assert Counter(row["route"] for row in first) == Counter({route: 20 for route in ROUTES})
    assert all(row["route"] == row["family"] for row in first)

    pairs: dict[str, list[dict]] = defaultdict(list)
    for row in first:
        pairs[str(row["pair_id"])].append(row)
    assert len(pairs) == 50
    route_pairs: Counter[tuple[str, str]] = Counter()
    for pair in pairs.values():
        assert len(pair) == 2
        left, right = sorted(pair, key=lambda row: row["pair_side"])
        assert left["route"] != right["route"]
        assert left["story_shell"] == right["story_shell"]
        assert left["decoy_route"] == right["route"] and right["decoy_route"] == left["route"]
        assert DECOYS[str(right["route"])] in str(left["prompt"])
        assert DECOYS[str(left["route"])] in str(right["prompt"])
        assert len(_words(str(left["prompt"]))) == len(_words(str(right["prompt"])))
        assert _numbers(str(left["prompt"])) == _numbers(str(right["prompt"]))
        route_pairs[tuple(sorted((str(left["route"]), str(right["route"]))))] += 1
    assert len(route_pairs) == 10 and set(route_pairs.values()) == {5}

    gold_violations: list[tuple[str, str]] = []
    v1_phrase_violations: list[tuple[str, str]] = []
    for row in first:
        prompt = str(row["prompt"]).lower()
        gold_violations.extend((str(row["id"]), phrase) for phrase in FORBIDDEN_GOLD_PHRASES if phrase.lower() in prompt)
        v1_phrase_violations.extend((str(row["id"]), phrase) for phrase in V1_DISTINCTIVE_RELATION_PHRASES if phrase.lower() in prompt)
        assert _relation_is_unambiguous(row), row["id"]
    assert not gold_violations
    assert not v1_phrase_violations

    assert V1_PROMPTS.exists(), V1_PROMPTS
    v1 = _read_jsonl(V1_PROMPTS)
    v1_texts = {str(row["prompt"]) for row in v1}
    v2_texts = {str(row["prompt"]) for row in first}
    exact_prompt_overlap = v1_texts & v2_texts
    v1_ngrams = set().union(*(_ngrams(text) for text in v1_texts))
    v2_ngrams = set().union(*(_ngrams(text) for text in v2_texts))
    long_ngram_overlap = v1_ngrams & v2_ngrams
    assert not exact_prompt_overlap
    assert not long_ngram_overlap, sorted(long_ngram_overlap)[:5]

    if not (DATA / "prompts.jsonl").exists():
        build(DATA)
    with tempfile.TemporaryDirectory() as directory:
        regenerated = Path(directory)
        build(regenerated)
        assert _sha(DATA / "prompts.jsonl") == _sha(regenerated / "prompts.jsonl")
        assert _sha(DATA / "manifest.json") == _sha(regenerated / "manifest.json")
    manifest = json.loads((DATA / "manifest.json").read_text(encoding="utf-8"))
    assert manifest["prompts_sha256"] == _sha(DATA / "prompts.jsonl")

    print(json.dumps({
        "status": "PASS",
        "prompts": len(first),
        "pairs": len(pairs),
        "route_counts": dict(sorted(Counter(row["route"] for row in first).items())),
        "route_pair_types": len(route_pairs),
        "examples_per_route_pair": next(iter(set(route_pairs.values()))),
        "matched_word_count_pairs": len(pairs),
        "matched_ordered_number_pairs": len(pairs),
        "unambiguous_relation_audits": sum(_relation_is_unambiguous(row) for row in first),
        "gold_phrase_violations": len(gold_violations),
        "v1_distinctive_relation_phrase_violations": len(v1_phrase_violations),
        "v1_exact_prompt_overlap": len(exact_prompt_overlap),
        "normalized_ngram_size": NGRAM_SIZE,
        "v1_long_normalized_ngram_overlap": len(long_ngram_overlap),
        "prompts_sha256": _sha(DATA / "prompts.jsonl"),
        "manifest_sha256": _sha(DATA / "manifest.json"),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

