#!/usr/bin/env python3
"""Generate matched relation-versus-decoy method-routing contrasts."""

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
SCHEMA_VERSION = 1
DEFAULT_SEED = 20260719
ROUTES = (
    "polynomial_value_obstruction",
    "diophantine_solvability",
    "modular_period_prime_filter",
    "finite_double_count",
    "finite_recurrence_period",
)
THEMES = (
    "archive desk",
    "materials laboratory",
    "transit office",
    "community garden",
    "repair workshop",
)
DECOY_NOUNS = {
    "polynomial_value_obstruction": "a polynomial catalogue",
    "diophantine_solvability": "a common-divisor ledger",
    "modular_period_prime_filter": "a power-cycle diagram",
    "finite_double_count": "an incidence table",
    "finite_recurrence_period": "a state-recurrence log",
}

# These include every route ID and the distinctive label phrases used by the
# ordinary method router. Individual wrong-route nouns remain allowed as decoys.
FORBIDDEN_NGRAMS = (
    *ROUTES,
    "congruence preservation",
    "integer polynomials",
    "input difference",
    "value difference",
    "greatest-common-divisor criterion",
    "linear diophantine",
    "bezout",
    "periodicity of modular powers",
    "exponent cycle",
    "residue classes",
    "double counting",
    "element incidences",
    "fixed element",
    "cycle detection",
    "finite recurrences",
    "repeated state",
    "cycle length",
)


def _rng(seed: int, *parts: object) -> random.Random:
    raw = ":".join(map(str, (seed, *parts))).encode()
    return random.Random(int.from_bytes(hashlib.sha256(raw).digest()[:8], "big"))


def _word_count(text: str) -> int:
    return len(re.findall(r"\b[\w'-]+\b", text))


def _numbers(text: str) -> list[str]:
    return re.findall(r"(?<![A-Za-z_])[+-]?\d+(?![A-Za-z_])", text)


PAD_SENTENCES = (
    (12, "Choose from the operative relations rather than from the surrounding story vocabulary."),
    (11, "Only the stated mathematical relations should determine the method choice here."),
    (9, "Narrative labels alone do not settle the mathematical choice."),
    (7, "Use the conditions, not the file title."),
    (6, "Base the choice on the relations."),
    (5, "Focus only on operative relations."),
    (4, "Briefly justify the choice."),
    (3, "Explain the choice."),
    (2, "Answer briefly."),
    (1, "Briefly."),
)


def _padding(words: int) -> str:
    parts: list[str] = []
    remaining = words
    while remaining:
        size, sentence = next((size, sentence) for size, sentence in PAD_SENTENCES if size <= remaining)
        parts.append(sentence)
        remaining -= size
    text = " ".join(parts)
    assert _word_count(text) == words
    return text


def _relation(route: str, values: tuple[int, int, int, int, int, int]) -> str:
    a, b, c, d, e, f = values
    if route == "polynomial_value_obstruction":
        return (
            f"A score rule assigns positions {a} and {b} the scores {c} and {d}, respectively. The rule must be built from the integer input, "
            f"integer constants, addition, and multiplication only. Decide whether both assignments can hold. Margin records {e} and {f} are unrelated."
        )
    if route == "diophantine_solvability":
        return (
            f"Two signed whole-number choices x and y contribute {a} units and {b} units per choice. Decide whether their combined total can be exactly {c}. "
            f"Shelf records {d}, {e}, and {f} are unrelated."
        )
    if route == "modular_period_prime_filter":
        return (
            f"Beginning from the multiplicative identity, repeatedly multiply by {a} and keep the remainder after division by {b}. "
            f"Find when remainder {c} occurs for exponents from {d} through {e}. Record {f} is unrelated."
        )
    if route == "finite_double_count":
        return (
            f"List every ordered choice of {a} groups drawn from a set of {b} objects. Across all lists, total how many objects occur in at least one chosen group. "
            f"Catalogue annotations {c}, {d}, {e}, and {f} are unrelated."
        )
    if route == "finite_recurrence_period":
        return (
            f"A pair begins at ({a}, {b}). Each move replaces (x, y) by (y, x plus {c} times y plus {d}), keeping each coordinate's remainder after division by {e}. "
            f"Determine the pair at step {f}."
        )
    raise ValueError(route)


def _shell(theme: str, decoy: str, relation: str, padding: str) -> str:
    return (
        f"At the {theme}, two analysts review the same style of numbered record. The file title mentions {decoy}, but that title is archival and imposes no condition. "
        f"{relation} {padding} State the single most useful mathematical method in ordinary English, and do not calculate the final answer."
    ).replace("  ", " ")


def _make_pair(seed: int, left_route: str, right_route: str, repeat: int) -> list[dict[str, object]]:
    rng = _rng(seed, left_route, right_route, repeat)
    # This ordered six-number signature is reused verbatim inside both prompts.
    values = (
        rng.randint(2, 5),
        rng.choice((7, 11, 13)),
        rng.randint(0, 6),
        rng.randint(2, 5),
        rng.randint(19, 41),
        rng.randint(101, 997),
    )
    theme = THEMES[repeat]
    left_relation = _relation(left_route, values)
    right_relation = _relation(right_route, values)
    common_suffix_words = _word_count(
        "State the single most useful mathematical method in ordinary English, and do not calculate the final answer."
    )
    left_base = _shell(theme, DECOY_NOUNS[right_route], left_relation, "")
    right_base = _shell(theme, DECOY_NOUNS[left_route], right_relation, "")
    target_words = max(_word_count(left_base), _word_count(right_base)) + 11
    left = _shell(theme, DECOY_NOUNS[right_route], left_relation, _padding(target_words - _word_count(left_base)))
    right = _shell(theme, DECOY_NOUNS[left_route], right_relation, _padding(target_words - _word_count(right_base)))
    assert _word_count(left) == _word_count(right) == target_words
    assert _numbers(left) == _numbers(right) == list(map(str, values))
    pair_key = f"{left_route}:{right_route}:{repeat}:{values}:{theme}"
    pair_hash = hashlib.sha256(pair_key.encode()).hexdigest()[:10]
    pair_id = f"mrc-v{SCHEMA_VERSION}-{ROUTES.index(left_route)}{ROUTES.index(right_route)}-{repeat}-{pair_hash}"
    result = []
    for side, route, prompt, decoy_route in (
        ("a", left_route, left, right_route),
        ("b", right_route, right, left_route),
    ):
        result.append(
            {
                "id": f"{pair_id}-{side}",
                "pair_id": pair_id,
                "pair_side": side,
                "family": route,
                "route": route,
                "decoy_route": decoy_route,
                "story_shell": theme,
                "prompt": prompt,
                "schema_version": SCHEMA_VERSION,
            }
        )
    return result


def generate_rows(seed: int = DEFAULT_SEED) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for left_route, right_route in combinations(ROUTES, 2):
        for repeat in range(5):
            rows.extend(_make_pair(seed, left_route, right_route, repeat))
    return rows


def write_jsonl(path: Path, rows: Iterable[dict[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build(output: Path, seed: int = DEFAULT_SEED) -> dict[str, object]:
    rows = generate_rows(seed)
    output.mkdir(parents=True, exist_ok=True)
    prompts_path = output / "prompts.jsonl"
    write_jsonl(prompts_path, rows)
    pairs = {row["pair_id"] for row in rows}
    route_counts = Counter(str(row["route"]) for row in rows)
    pair_type_counts = Counter(
        tuple(sorted(str(row["route"]) for row in rows if row["pair_id"] == pair_id))
        for pair_id in pairs
    )
    word_counts = [_word_count(str(row["prompt"])) for row in rows]
    manifest: dict[str, object] = {
        "schema_version": SCHEMA_VERSION,
        "seed": seed,
        "purpose": "matched contrast and decoy evaluation of natural-language method selection",
        "scope": "route selection only; no fixed-executor or Lean certification is claimed",
        "routes": list(ROUTES),
        "count": len(rows),
        "pairs": len(pairs),
        "route_counts": dict(sorted(route_counts.items())),
        "pair_type_counts": {" + ".join(pair): count for pair, count in sorted(pair_type_counts.items())},
        "pair_contract": {
            "same_story_shell": True,
            "same_word_count": True,
            "same_ordered_numeric_literals": True,
            "different_correct_routes": True,
            "counterpart_route_is_salient_nonoperative_decoy": True,
        },
        "word_count_range": [min(word_counts), max(word_counts)],
        "forbidden_ngrams": list(FORBIDDEN_NGRAMS),
        "prompts_sha256": sha256(prompts_path),
        "limitations": [
            "This suite evaluates route selection, not proof generation or final-answer correctness.",
            "The cross-route story shells do not share one universal fixed executor.",
            "No Lean certification is claimed for the synthetic cross-route prompts.",
            "Matching controls length and ordered numeric literals but cannot make mathematical vocabulary identical.",
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
