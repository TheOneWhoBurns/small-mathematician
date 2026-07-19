#!/usr/bin/env python3
"""Validate v3 structure, semantics, seals, and separation from v1 and v2."""

from __future__ import annotations

import hashlib
import json
import re
import tempfile
from collections import Counter, defaultdict
from pathlib import Path

from generate import (
    DATA, DECOYS, FORBIDDEN_GOLD_PHRASES, RELATION_AUDIT_TERMS, ROUTES, SEALED_PROBES,
    V1_DISTINCTIVE_PHRASES, V2_DISTINCTIVE_PHRASES, build, generate_rows,
)


METHOD_ROUTER = Path(__file__).resolve().parents[1]
PRIOR_PROMPTS = {
    "v1": METHOD_ROUTER / "contrast" / "data" / "prompts.jsonl",
    "v2": METHOD_ROUTER / "contrast_v2" / "data" / "prompts.jsonl",
}
PROJECT = Path(__file__).resolve().parents[3]
SEAL_PATHS = {
    "iter039": PROJECT / "runs" / "iter039-frozen-layer21-contrast-trained-iter014-sealed" / "selection-seal.json",
    "base": PROJECT / "runs" / "iter039b-frozen-layer21-contrast-trained-base-sealed" / "selection-seal.json",
}
NGRAM_SIZE = 8


def _read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def _words(text: str) -> list[str]:
    return re.findall(r"\b[\w'-]+\b", text)


def _numbers(text: str) -> list[str]:
    return re.findall(r"(?<![A-Za-z_])[+-]?\d+(?![A-Za-z_])", text)


def _normalized_tokens(text: str) -> list[str]:
    return re.findall(r"[a-z]+|<num>", re.sub(r"[+-]?\d+", " <num> ", text.lower()))


def _ngrams(text: str) -> set[tuple[str, ...]]:
    tokens = _normalized_tokens(text)
    return {tuple(tokens[index:index + NGRAM_SIZE]) for index in range(len(tokens) - NGRAM_SIZE + 1)}


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _semantic_audit(row: dict) -> bool:
    prompt, route = str(row["prompt"]).lower(), str(row["route"])
    if not all(term in prompt for term in RELATION_AUDIT_TERMS[route]):
        return False
    values = list(map(int, _numbers(prompt)))
    if len(values) != 6:
        return False
    a, b, c, d, e, f = values
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
    rows = generate_rows()
    assert rows == generate_rows()
    assert len(rows) == 100 and len({row["id"] for row in rows}) == 100
    assert len({row["prompt"] for row in rows}) == 100
    route_counts = Counter(row["route"] for row in rows)
    assert route_counts == Counter({route: 20 for route in ROUTES})
    assert all(row["route"] == row["family"] for row in rows)

    pairs: dict[str, list[dict]] = defaultdict(list)
    for row in rows:
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
    v2_phrase_violations: list[tuple[str, str]] = []
    for row in rows:
        prompt = str(row["prompt"]).lower()
        gold_violations.extend((str(row["id"]), phrase) for phrase in FORBIDDEN_GOLD_PHRASES if phrase.lower() in prompt)
        v1_phrase_violations.extend((str(row["id"]), phrase) for phrase in V1_DISTINCTIVE_PHRASES if phrase.lower() in prompt)
        v2_phrase_violations.extend((str(row["id"]), phrase) for phrase in V2_DISTINCTIVE_PHRASES if phrase.lower() in prompt)
        assert _semantic_audit(row), row["id"]
    assert not gold_violations and not v1_phrase_violations and not v2_phrase_violations

    v3_texts = {str(row["prompt"]) for row in rows}
    v3_ngrams = set().union(*(_ngrams(text) for text in v3_texts))
    comparisons: dict[str, dict[str, int]] = {}
    for version, path in PRIOR_PROMPTS.items():
        assert path.exists(), path
        prior_texts = {str(row["prompt"]) for row in _read_jsonl(path)}
        prior_ngrams = set().union(*(_ngrams(text) for text in prior_texts))
        exact_overlap = v3_texts & prior_texts
        ngram_overlap = v3_ngrams & prior_ngrams
        assert not exact_overlap
        assert not ngram_overlap, (version, sorted(ngram_overlap)[:5])
        comparisons[version] = {"exact_prompt_overlap": len(exact_overlap), "normalized_8gram_overlap": len(ngram_overlap)}

    for name, path in SEAL_PATHS.items():
        assert path.exists(), path
        seal = json.loads(path.read_text(encoding="utf-8"))
        assert seal["probe_sha256"] == SEALED_PROBES[name]["probe_sha256"]
        assert _sha(path) == SEALED_PROBES[name]["selection_seal_sha256"]

    if not (DATA / "prompts.jsonl").exists():
        build(DATA)
    with tempfile.TemporaryDirectory() as directory:
        regenerated = Path(directory)
        build(regenerated)
        assert _sha(DATA / "prompts.jsonl") == _sha(regenerated / "prompts.jsonl")
        assert _sha(DATA / "manifest.json") == _sha(regenerated / "manifest.json")
    manifest = json.loads((DATA / "manifest.json").read_text(encoding="utf-8"))
    assert manifest["prompts_sha256"] == _sha(DATA / "prompts.jsonl")
    assert manifest["sealed_before_v3"] == SEALED_PROBES

    print(json.dumps({
        "status": "PASS",
        "prompts": len(rows),
        "pairs": len(pairs),
        "route_counts": dict(sorted(route_counts.items())),
        "route_pair_types": len(route_pairs),
        "examples_per_route_pair": next(iter(set(route_pairs.values()))),
        "matched_word_count_pairs": len(pairs),
        "matched_ordered_number_pairs": len(pairs),
        "semantic_audits_passed": sum(_semantic_audit(row) for row in rows),
        "gold_phrase_violations": len(gold_violations),
        "v1_distinctive_phrase_violations": len(v1_phrase_violations),
        "v2_distinctive_phrase_violations": len(v2_phrase_violations),
        "prior_version_overlap": comparisons,
        "normalized_ngram_size": NGRAM_SIZE,
        "sealed_probe_hashes_verified": SEALED_PROBES,
        "prompts_sha256": _sha(DATA / "prompts.jsonl"),
        "manifest_sha256": _sha(DATA / "manifest.json"),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

