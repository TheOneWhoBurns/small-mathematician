#!/usr/bin/env python3
"""Generate the third, newly authored sealed method-routing contrast set."""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import re
from collections import Counter
from itertools import combinations
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parent
DATA = ROOT / "data"
SCHEMA_VERSION = 3
DEFAULT_SEED = 20260721
ROUTES = (
    "polynomial_value_obstruction",
    "diophantine_solvability",
    "modular_period_prime_filter",
    "finite_double_count",
    "finite_recurrence_period",
)
STORY_SHELLS = (
    "mountain weather outpost",
    "theater rigging loft",
    "hospital supply alcove",
    "river monitoring pier",
    "library digitization bay",
)
DECOYS = {
    "polynomial_value_obstruction": "a polynomial reference tab",
    "diophantine_solvability": "a gcd worksheet emblem",
    "modular_period_prime_filter": "a modular-exponent ribbon",
    "finite_double_count": "an incidence-counting caption",
    "finite_recurrence_period": "a recurrence-cycle watermark",
}
SEALED_PROBES = {
    "iter039": {
        "probe_sha256": "d729c596f2c209f1f8df7adb7e592cda8de9571915a481b9d73bbd69af89efd7",
        "selection_seal_sha256": "13ea9855a72984849590bb24a12499c5dc79b17be3cc8df3cac12e60b3394490",
    },
    "base": {
        "probe_sha256": "bdaae51db013fa520ef6ef516fd6deae303275ae59d327bf9b7fade1dcba2795",
        "selection_seal_sha256": "64f1c5021752551cc7bb2bdd15028cfbf860063c27c5cbc1295f6d517860c084",
    },
}
FORBIDDEN_GOLD_PHRASES = (
    *ROUTES,
    "congruence preservation for integer polynomials",
    "greatest-common-divisor criterion for linear diophantine equations",
    "periodicity of modular powers",
    "double counting of element incidences",
    "cycle detection for finite recurrences",
    "congruence preservation",
    "greatest-common-divisor criterion",
    "periodicity of modular powers",
    "double counting",
    "cycle detection",
    "bezout witness",
)
V1_DISTINCTIVE_PHRASES = (
    "a score rule assigns positions",
    "the rule must be built from the integer input",
    "two signed whole-number choices",
    "their combined total can be exactly",
    "beginning from the multiplicative identity",
    "repeatedly multiply by",
    "keep the remainder after division",
    "list every ordered choice",
    "occur in at least one chosen group",
    "a pair begins at",
    "each move replaces",
)
V2_DISTINCTIVE_PHRASES = (
    "starting from a whole-number dial reading",
    "whole-number coefficients through finitely many sums and products",
    "positive or negative number of crates",
    "net load can reach exactly",
    "scaling the current mark",
    "the target mark is",
    "complete catalogue of sequences",
    "aggregate the marked-badge counts",
    "two-register memory initialized",
    "on each clock tick",
)
RELATION_AUDIT_TERMS = {
    "polynomial_value_obstruction": (
        "integer knob setting",
        "nonnegative whole power",
        "integer multiple",
        "same machine",
    ),
    "diophantine_solvability": (
        "add or remove any whole count",
        "token values",
        "account balance",
        "attainable",
    ),
    "modular_period_prime_filter": (
        "circular display",
        "every pulse scales",
        "wrapped back",
        "pulse numbers",
    ),
    "finite_double_count": (
        "every possible portion",
        "distinct labels touched",
        "sum those counts over the full inventory",
    ),
    "finite_recurrence_period": (
        "two memory cells",
        "during an update",
        "old right value",
        "update number",
    ),
}


def _rng(seed: int, *parts: object) -> random.Random:
    raw = ":".join(map(str, (seed, *parts))).encode()
    return random.Random(int.from_bytes(hashlib.sha256(raw).digest()[:8], "big"))


def _words(text: str) -> list[str]:
    return re.findall(r"\b[\w'-]+\b", text)


def _numbers(text: str) -> list[str]:
    return re.findall(r"(?<![A-Za-z_])[+-]?\d+(?![A-Za-z_])", text)


PAD_TEXTS = (
    "A method should follow the binding relationship rather than the obsolete visual annotation.",
    "Use the actual constraint structure and disregard superficial filing terminology.",
    "Decorative classifications supply no mathematical evidence for this choice.",
    "Concentrate on how the listed quantities interact.",
    "Select from the binding relationship alone.",
    "Give a compact reason for selecting it.",
    "Support the selection succinctly.",
    "Answer with care.",
    "Respond concisely.",
    "Briefly.",
)


def _padding(word_count: int) -> str:
    remaining = word_count
    parts: list[str] = []
    options = sorted(((len(_words(text)), text) for text in PAD_TEXTS), reverse=True)
    for size, text in options:
        if size <= remaining:
            parts.append(text)
            remaining -= size
        if remaining == 0:
            break
    if remaining:
        raise ValueError(f"cannot form {word_count} words of nonrepeating padding")
    result = " ".join(parts)
    assert len(_words(result)) == word_count
    return result


def _relation(route: str, values: tuple[int, int, int, int, int, int]) -> str:
    a, b, c, d, e, f = values
    if route == "polynomial_value_obstruction":
        return (
            f"A machine accepts an integer knob setting. Its output is a finite sum of terms, each an integer multiple of a nonnegative whole power of that setting. "
            f"The log says settings {a} and {b} yield outputs {c} and {d}. Decide whether the same machine can produce both entries. Serial marks {e} and {f} are irrelevant."
        )
    if route == "diophantine_solvability":
        return (
            f"A cashier may add or remove any whole count of two token values, {a} credits and {b} credits. Decide whether account balance {c} is attainable. "
            f"Receipt marks {d}, {e}, and {f} are irrelevant."
        )
    if route == "modular_period_prime_filter":
        return (
            f"Every pulse scales the current position by {a} on a circular display with {b} positions, with overflow wrapped back around the display. "
            f"For desired position {c}, identify the pulse numbers between {d} and {e} that reach it. Batch mark {f} is irrelevant."
        )
    if route == "finite_double_count":
        return (
            f"Build an inventory of rows with {a} slots, where each slot holds every possible portion of a collection containing {b} labels. In each row record the number of distinct labels touched, then sum those counts over the full inventory. "
            f"Index marks {c}, {d}, {e}, and {f} are irrelevant."
        )
    if route == "finite_recurrence_period":
        return (
            f"A device starts with two memory cells holding {a} and {b}. During an update, the left cell takes the old right value, while the right cell takes the old left plus {c} times the old right plus {d}; values wrap after {e}. "
            f"Find both cells after update number {f}."
        )
    raise ValueError(route)


def _frame(shell: str, decoy: str, relation: str, padding: str) -> str:
    text = (
        f"A coordinator working at the {shell} opens an unfamiliar numerical case. The cover bears {decoy}. That cover mark belongs to an obsolete filing system and has no force in the case. "
        f"{relation} {padding} Identify the mathematical principle that most directly resolves the operative question. Answer in ordinary language without carrying out the requested calculation."
    )
    return re.sub(r"\s+", " ", text).strip()


def _make_pair(seed: int, route_a: str, route_b: str, repeat: int) -> list[dict[str, object]]:
    rng = _rng(seed, route_a, route_b, repeat)
    values = (
        rng.randint(4, 8),
        rng.choice((17, 19, 23)),
        rng.randint(0, 10),
        rng.randint(4, 9),
        rng.randint(83, 131),
        rng.randint(5003, 9001),
    )
    shell = STORY_SHELLS[repeat]
    relation_a, relation_b = _relation(route_a, values), _relation(route_b, values)
    base_a, base_b = _frame(shell, DECOYS[route_b], relation_a, ""), _frame(shell, DECOYS[route_a], relation_b, "")
    target_words = max(len(_words(base_a)), len(_words(base_b))) + 13
    prompt_a = _frame(shell, DECOYS[route_b], relation_a, _padding(target_words - len(_words(base_a))))
    prompt_b = _frame(shell, DECOYS[route_a], relation_b, _padding(target_words - len(_words(base_b))))
    assert len(_words(prompt_a)) == len(_words(prompt_b)) == target_words
    assert _numbers(prompt_a) == _numbers(prompt_b) == list(map(str, values))
    material = f"v3:{route_a}:{route_b}:{repeat}:{values}:{shell}"
    pair_hash = hashlib.sha256(material.encode()).hexdigest()[:10]
    pair_id = f"mrc-v3-{ROUTES.index(route_a)}{ROUTES.index(route_b)}-{repeat}-{pair_hash}"
    return [
        {"id": f"{pair_id}-a", "pair_id": pair_id, "pair_side": "a", "family": route_a, "route": route_a,
         "decoy_route": route_b, "story_shell": shell, "prompt": prompt_a, "schema_version": SCHEMA_VERSION},
        {"id": f"{pair_id}-b", "pair_id": pair_id, "pair_side": "b", "family": route_b, "route": route_b,
         "decoy_route": route_a, "story_shell": shell, "prompt": prompt_b, "schema_version": SCHEMA_VERSION},
    ]


def generate_rows(seed: int = DEFAULT_SEED) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for route_a, route_b in combinations(ROUTES, 2):
        for repeat in range(5):
            rows.extend(_make_pair(seed, route_a, route_b, repeat))
    return rows


def write_jsonl(path: Path, rows: Iterable[dict[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build(output: Path = DATA, seed: int = DEFAULT_SEED) -> dict[str, object]:
    rows = generate_rows(seed)
    output.mkdir(parents=True, exist_ok=True)
    prompt_path = output / "prompts.jsonl"
    write_jsonl(prompt_path, rows)
    route_counts = Counter(str(row["route"]) for row in rows)
    pairs = {str(row["pair_id"]) for row in rows}
    pair_types = Counter(tuple(sorted(str(row["route"]) for row in rows if row["pair_id"] == pair_id)) for pair_id in pairs)
    manifest: dict[str, object] = {
        "schema_version": SCHEMA_VERSION,
        "seed": seed,
        "purpose": "third newly authored held-out matched routing test created after the named probes were sealed",
        "scope": "route-selection evaluation only; no model evaluation, proof executor, or Lean certification",
        "sealed_before_v3": SEALED_PROBES,
        "routes": list(ROUTES),
        "count": len(rows),
        "pairs": len(pairs),
        "route_counts": dict(sorted(route_counts.items())),
        "pair_type_counts": {" + ".join(pair): count for pair, count in sorted(pair_types.items())},
        "pair_contract": {
            "third_relation_phrasings": True,
            "third_story_shells": True,
            "same_word_count": True,
            "same_ordered_numeric_literals": True,
            "different_correct_routes": True,
            "counterpart_route_is_nonoperative_decoy": True,
        },
        "prior_version_comparison_contract": {
            "versions": ["contrast_v1", "contrast_v2"],
            "exact_prompt_overlap_required_each": 0,
            "normalized_ngram_size": 8,
            "long_normalized_ngram_overlap_required_each": 0,
        },
        "forbidden_gold_phrases": list(FORBIDDEN_GOLD_PHRASES),
        "forbidden_v1_relation_phrases": list(V1_DISTINCTIVE_PHRASES),
        "forbidden_v2_relation_phrases": list(V2_DISTINCTIVE_PHRASES),
        "prompts_sha256": sha256(prompt_path),
        "limitations": [
            "This evaluates method routing only, not proof generation or answer correctness.",
            "The semantic audit checks authored relation contracts and parameter well-formedness; it is not based on model consensus.",
            "Pair matching controls story, length, and numeric sequence, while relation-specific vocabulary necessarily differs.",
            "The held-out claim applies only because the recorded probes and their configuration seals predate v3 inspection.",
        ],
    }
    (output / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return manifest


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=DEFAULT_SEED)
    parser.add_argument("--output", type=Path, default=DATA)
    args = parser.parse_args()
    print(json.dumps(build(args.output, args.seed), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
