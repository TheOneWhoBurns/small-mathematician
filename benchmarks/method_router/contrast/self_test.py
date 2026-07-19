#!/usr/bin/env python3
"""Validate deterministic counts, matching, decoys, and lexical boundaries."""

from __future__ import annotations

import hashlib
import json
import re
import tempfile
from collections import Counter, defaultdict
from pathlib import Path

from generate import DATA, DECOY_NOUNS, FORBIDDEN_NGRAMS, ROUTES, build, generate_rows


def words(text: str) -> list[str]:
    return re.findall(r"\b[\w'-]+\b", text)


def numbers(text: str) -> list[str]:
    return re.findall(r"(?<![A-Za-z_])[+-]?\d+(?![A-Za-z_])", text)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    first, second = generate_rows(), generate_rows()
    assert first == second
    assert len(first) == 100
    assert len({row["id"] for row in first}) == 100
    assert len({row["prompt"] for row in first}) == 100

    route_counts = Counter(row["route"] for row in first)
    assert route_counts == Counter({route: 20 for route in ROUTES})
    assert all(row["family"] == row["route"] for row in first)

    by_pair: dict[str, list[dict]] = defaultdict(list)
    for row in first:
        by_pair[str(row["pair_id"])].append(row)
    assert len(by_pair) == 50
    route_pair_counts: Counter[tuple[str, str]] = Counter()
    for pair_id, pair in by_pair.items():
        assert len(pair) == 2, pair_id
        pair.sort(key=lambda row: row["pair_side"])
        left, right = pair
        assert {left["pair_side"], right["pair_side"]} == {"a", "b"}
        assert left["route"] != right["route"]
        assert left["decoy_route"] == right["route"] and right["decoy_route"] == left["route"]
        assert left["story_shell"] == right["story_shell"]
        assert len(words(str(left["prompt"]))) == len(words(str(right["prompt"])))
        assert numbers(str(left["prompt"])) == numbers(str(right["prompt"]))
        assert DECOY_NOUNS[str(right["route"])] in str(left["prompt"])
        assert DECOY_NOUNS[str(left["route"])] in str(right["prompt"])
        route_pair_counts[tuple(sorted((str(left["route"]), str(right["route"]))))] += 1
    assert len(route_pair_counts) == 10
    assert set(route_pair_counts.values()) == {5}

    violations: list[tuple[str, str]] = []
    for row in first:
        lowered = str(row["prompt"]).lower()
        for phrase in FORBIDDEN_NGRAMS:
            if phrase.lower() in lowered:
                violations.append((str(row["id"]), phrase))
    assert not violations, violations[:5]

    # Regeneration into an isolated directory must be byte-identical.
    if not (DATA / "prompts.jsonl").exists():
        build(DATA)
    with tempfile.TemporaryDirectory() as directory:
        regenerated = Path(directory)
        build(regenerated)
        assert digest(DATA / "prompts.jsonl") == digest(regenerated / "prompts.jsonl")
        assert digest(DATA / "manifest.json") == digest(regenerated / "manifest.json")

    manifest = json.loads((DATA / "manifest.json").read_text(encoding="utf-8"))
    assert manifest["prompts_sha256"] == digest(DATA / "prompts.jsonl")
    assert manifest["scope"].startswith("route selection only")
    print(json.dumps({
        "status": "PASS",
        "prompts": len(first),
        "pairs": len(by_pair),
        "route_counts": dict(sorted(route_counts.items())),
        "route_pair_types": len(route_pair_counts),
        "examples_per_route_pair": sorted(set(route_pair_counts.values())).pop(),
        "forbidden_ngram_violations": len(violations),
        "exact_word_matched_pairs": len(by_pair),
        "exact_number_sequence_matched_pairs": len(by_pair),
        "prompts_sha256": digest(DATA / "prompts.jsonl"),
        "manifest_sha256": digest(DATA / "manifest.json"),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

