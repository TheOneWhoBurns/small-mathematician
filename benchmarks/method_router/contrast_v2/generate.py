#!/usr/bin/env python3
"""Generate the held-out v2 relation-versus-decoy routing contrasts."""

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
SCHEMA_VERSION = 2
DEFAULT_SEED = 20260720
ROUTES = (
    "polynomial_value_obstruction",
    "diophantine_solvability",
    "modular_period_prime_filter",
    "finite_double_count",
    "finite_recurrence_period",
)
STORY_SHELLS = (
    "observatory console",
    "harbor dispatch booth",
    "museum conservation room",
    "bakery planning bench",
    "wildlife survey station",
)
DECOYS = {
    "polynomial_value_obstruction": "a polynomial display card",
    "diophantine_solvability": "a divisor-equation sticker",
    "modular_period_prime_filter": "a residue-power label",
    "finite_double_count": "a membership-tally header",
    "finite_recurrence_period": "a recurrence-state stamp",
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
V1_DISTINCTIVE_RELATION_PHRASES = (
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
RELATION_AUDIT_TERMS = {
    "polynomial_value_obstruction": (
        "whole-number dial reading",
        "whole-number coefficients",
        "finitely many sums and products",
        "two reported outputs",
    ),
    "diophantine_solvability": (
        "positive or negative number of crates",
        "net load",
        "reach exactly",
    ),
    "modular_period_prime_filter": (
        "scaling the current mark",
        "division remainder",
        "time labels",
    ),
    "finite_double_count": (
        "complete catalogue of sequences",
        "seen at least once",
        "aggregate the marked-badge counts",
    ),
    "finite_recurrence_period": (
        "two-register memory",
        "on each clock tick",
        "later tick",
    ),
}


def _rng(seed: int, *parts: object) -> random.Random:
    payload = ":".join(map(str, (seed, *parts))).encode()
    return random.Random(int.from_bytes(hashlib.sha256(payload).digest()[:8], "big"))


def _words(text: str) -> list[str]:
    return re.findall(r"\b[\w'-]+\b", text)


def _numbers(text: str) -> list[str]:
    return re.findall(r"(?<![A-Za-z_])[+-]?\d+(?![A-Za-z_])", text)


PAD = (
    (12, "The operative dependency matters more than any decorative vocabulary printed around it."),
    (11, "Select by the mathematical dependency and disregard the decorative filing language."),
    (8, "Decorative wording should not control the mathematical decision."),
    (8, "Attend to what the quantities must satisfy together."),
    (7, "Use only the dependency among the quantities."),
    (6, "Choose from the operative dependency alone."),
    (5, "Attend only to the dependency."),
    (4, "Give one concise reason."),
    (3, "Justify the selection."),
    (2, "Respond briefly."),
    (1, "Briefly."),
)


def _padding(word_count: int) -> str:
    remaining = word_count
    parts: list[str] = []
    for size, text in PAD:
        if size <= remaining:
            parts.append(text)
            remaining -= size
        if remaining == 0:
            break
    if remaining:
        raise ValueError(f"cannot form natural padding of {word_count} words")
    result = " ".join(parts)
    assert len(_words(result)) == word_count
    return result


def _operative_relation(route: str, values: tuple[int, int, int, int, int, int]) -> str:
    a, b, c, d, e, f = values
    if route == "polynomial_value_obstruction":
        return (
            f"Starting from a whole-number dial reading, an evaluator may combine that reading with whole-number coefficients through finitely many sums and products. "
            f"Two reported outputs claim that readings {a} and {b} produce {c} and {d}. Determine whether one evaluator can honor both reports. Notes {e} and {f} have no bearing."
        )
    if route == "diophantine_solvability":
        return (
            f"A shipment may include any positive or negative number of crates weighing {a} and {b} units. Decide whether its net load can reach exactly {c} units. "
            f"Inspection tags {d}, {e}, and {f} have no bearing."
        )
    if route == "modular_period_prime_filter":
        return (
            f"A display advances by scaling the current mark by {a}, then retaining only its division remainder for divisor {b}. "
            f"The target mark is {c}; identify its time labels from {d} through {e}. Tag {f} has no bearing."
        )
    if route == "finite_double_count":
        return (
            f"Form the complete catalogue of sequences containing {a} selections from {b} badges. For every sequence, mark each badge seen at least once, then aggregate the marked-badge counts over the catalogue. "
            f"Annotations {c}, {d}, {e}, and {f} have no bearing."
        )
    if route == "finite_recurrence_period":
        return (
            f"A controller has two-register memory initialized to ({a}, {b}). On each clock tick the second register becomes first, while the new second is the old first plus {c} times the old second plus {d}, all reduced by divisor {e}. "
            f"Find the memory contents at later tick {f}."
        )
    raise ValueError(route)


def _frame(shell: str, decoy: str, relation: str, padding: str) -> str:
    parts = (
        f"Inside the {shell}, a reviewer receives a fresh quantitative brief. A decorative badge reads {decoy}; the badge was attached by an archivist and contributes no constraint. "
        f"{relation} {padding} Name one mathematical approach that directly exploits the operative relationship. Reply in natural language without working out the numerical result."
    )
    return re.sub(r"\s+", " ", parts).strip()


def _make_pair(seed: int, route_a: str, route_b: str, repeat: int) -> list[dict[str, object]]:
    rng = _rng(seed, route_a, route_b, repeat)
    values = (
        rng.randint(3, 6),
        rng.choice((11, 13, 17)),
        rng.randint(0, 8),
        rng.randint(3, 7),
        rng.randint(43, 79),
        rng.randint(1009, 4001),
    )
    shell = STORY_SHELLS[repeat]
    relation_a = _operative_relation(route_a, values)
    relation_b = _operative_relation(route_b, values)
    base_a = _frame(shell, DECOYS[route_b], relation_a, "")
    base_b = _frame(shell, DECOYS[route_a], relation_b, "")
    target_words = max(len(_words(base_a)), len(_words(base_b))) + 12
    prompt_a = _frame(shell, DECOYS[route_b], relation_a, _padding(target_words - len(_words(base_a))))
    prompt_b = _frame(shell, DECOYS[route_a], relation_b, _padding(target_words - len(_words(base_b))))
    assert len(_words(prompt_a)) == len(_words(prompt_b)) == target_words
    assert _numbers(prompt_a) == _numbers(prompt_b) == list(map(str, values))
    material = f"v2:{route_a}:{route_b}:{repeat}:{values}:{shell}"
    pair_hash = hashlib.sha256(material.encode()).hexdigest()[:10]
    pair_id = f"mrc-v2-{ROUTES.index(route_a)}{ROUTES.index(route_b)}-{repeat}-{pair_hash}"
    return [
        {
            "id": f"{pair_id}-a",
            "pair_id": pair_id,
            "pair_side": "a",
            "family": route_a,
            "route": route_a,
            "decoy_route": route_b,
            "story_shell": shell,
            "prompt": prompt_a,
            "schema_version": SCHEMA_VERSION,
        },
        {
            "id": f"{pair_id}-b",
            "pair_id": pair_id,
            "pair_side": "b",
            "family": route_b,
            "route": route_b,
            "decoy_route": route_a,
            "story_shell": shell,
            "prompt": prompt_b,
            "schema_version": SCHEMA_VERSION,
        },
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
    pair_ids = {str(row["pair_id"]) for row in rows}
    pair_type_counts = Counter(
        tuple(sorted(str(row["route"]) for row in rows if row["pair_id"] == pair_id))
        for pair_id in pair_ids
    )
    manifest: dict[str, object] = {
        "schema_version": SCHEMA_VERSION,
        "seed": seed,
        "purpose": "new held-out matched relation and counterdecoy test for a router fixed on contrast v1",
        "scope": "route-selection evaluation only; no model training, executor validation, or Lean claim",
        "routes": list(ROUTES),
        "count": len(rows),
        "pairs": len(pair_ids),
        "route_counts": dict(sorted(route_counts.items())),
        "pair_type_counts": {" + ".join(pair): count for pair, count in sorted(pair_type_counts.items())},
        "pair_contract": {
            "new_story_shells": True,
            "new_relation_phrasings": True,
            "same_word_count": True,
            "same_ordered_numeric_literals": True,
            "different_correct_routes": True,
            "counterpart_route_is_nonoperative_decoy": True,
        },
        "v1_comparison_contract": {
            "exact_prompt_overlap_required": 0,
            "normalized_ngram_size": 8,
            "long_normalized_ngram_overlap_required": 0,
        },
        "forbidden_gold_phrases": list(FORBIDDEN_GOLD_PHRASES),
        "forbidden_v1_relation_phrases": list(V1_DISTINCTIVE_RELATION_PHRASES),
        "prompts_sha256": sha256(prompt_path),
        "limitations": [
            "This is a controlled method-selection test, not a proof or final-answer benchmark.",
            "Unambiguity is established from the authored mathematical contracts and structural audits, not from model agreement.",
            "Matching controls story shell, word count, and numeric sequence within pairs, but operative vocabulary must differ because the relations differ.",
            "The set is held out only if configuration and model selection were already frozen before inspecting v2 results.",
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
