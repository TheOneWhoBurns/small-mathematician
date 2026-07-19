#!/usr/bin/env python3
"""Core generator, strict English parsers, and oracle for the verified-plan ladder."""

from __future__ import annotations

import hashlib
import json
import math
import random
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parent
DATA = ROOT / "data"
SCHEMA_VERSION = 1
DEFAULT_SEED = 20260719
SPLIT_COUNTS = {"train": 60, "valid": 10, "train_fit": 10, "near": 16, "paraphrase": 16, "composition": 16}
FAMILIES = (
    "polynomial_value_obstruction",
    "diophantine_solvability",
    "modular_period_prime_filter",
    "finite_double_count",
    "finite_recurrence_period",
)
EVAL_SPLITS = ("valid", "train_fit", "near", "paraphrase", "composition")


@dataclass(frozen=True)
class Instance:
    id: str
    family: str
    split: str
    semantic_instance_id: str
    parameter_hash: str
    graph_id: str
    prompt_template_id: str
    prompt: str
    target_free: str
    target_ordered: str
    parameters: dict[str, Any]
    required_facts: list[dict[str, Any]]
    conclusion: dict[str, Any]

    def public(self) -> dict[str, Any]:
        return {
            "id": self.id,
            "family": self.family,
            "split": self.split,
            "semantic_instance_id": self.semantic_instance_id,
            "parameter_hash": self.parameter_hash,
            "graph_id": self.graph_id,
            "prompt_template_id": self.prompt_template_id,
            "prompt": self.prompt,
            "schema_version": SCHEMA_VERSION,
        }

    def targets(self) -> dict[str, Any]:
        return {
            "id": self.id,
            "family": self.family,
            "split": self.split,
            "target_free": self.target_free,
            "target_ordered": self.target_ordered,
            "schema_version": SCHEMA_VERSION,
        }

    def private(self) -> dict[str, Any]:
        return {
            "id": self.id,
            "family": self.family,
            "split": self.split,
            "semantic_instance_id": self.semantic_instance_id,
            "parameter_hash": self.parameter_hash,
            "graph_id": self.graph_id,
            "prompt_template_id": self.prompt_template_id,
            "parameters": self.parameters,
            "required_facts": self.required_facts,
            "conclusion": self.conclusion,
            "schema_version": SCHEMA_VERSION,
        }


def _stable_rng(seed: int, *parts: object) -> random.Random:
    payload = ":".join(map(str, (seed, *parts))).encode()
    return random.Random(int.from_bytes(hashlib.sha256(payload).digest()[:8], "big"))


def _parameter_hash(parameters: dict[str, Any]) -> str:
    raw = json.dumps(parameters, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(raw).hexdigest()[:12]


def _extended_gcd(a: int, b: int) -> tuple[int, int, int]:
    old_r, r, old_s, s, old_t, t = a, b, 1, 0, 0, 1
    while r:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s - q * s
        old_t, t = t, old_t - q * t
    return old_r, old_s, old_t


def _is_prime(n: int) -> bool:
    if n < 2:
        return False
    return all(n % d for d in range(2, math.isqrt(n) + 1))


def _multiplicative_order(base: int, modulus: int) -> int:
    value = 1
    for period in range(1, modulus * modulus + 1):
        value = value * base % modulus
        if value == 1:
            return period
    raise ValueError("no multiplicative order")


def _fmt_list(values: list[int]) -> str:
    return ", ".join(map(str, values)) if values else "none"


def _words(text: str) -> list[str]:
    return re.findall(r"\b[\w'-]+\b", text)


FILLERS = (
    "",
    "These checks expose every essential claim for direct independent verification.",
    "These explicit numerical checks record the mathematical reason, making every essential intermediate claim visible for direct independent verification.",
    "These explicit numerical checks record the mathematical reason for the conclusion, so the argument can be verified independently from the quantities stated in the problem. They also make every essential intermediate claim visible for direct checking.",
)


def _make_targets(sentences: list[str], free_order: list[int] | None = None) -> tuple[str, str]:
    """Build matched ordinary-English targets with exactly three connector words."""
    if len(sentences) < 3:
        raise ValueError("targets need at least two facts and a conclusion")
    fact_sentences, conclusion = sentences[:-1], sentences[-1]
    if free_order is None:
        free_order = list(range(len(fact_sentences)))
        if len(free_order) >= 3:
            free_order = free_order[1:2] + free_order[:1] + free_order[2:]
    base_free = [*(fact_sentences[index] for index in free_order), conclusion]
    candidates = [(" ".join(part for part in [*base_free[:-1], filler, conclusion] if part), filler) for filler in FILLERS]
    fitting = [(candidate, filler) for candidate, filler in candidates if 60 <= len(_words(candidate)) <= 90]
    if not fitting:
        raise AssertionError(f"no filler fits bare target with {len(_words(' '.join(base_free)))} words")
    free, filler = max(fitting, key=lambda pair: len(_words(pair[0])))
    ordered_facts = fact_sentences.copy()
    ordered_facts[0] = "First, " + ordered_facts[0]
    ordered_facts[1] = "Next, " + ordered_facts[1]
    # Remove one noncritical filler word to offset connector tokenization while
    # preserving the exact same critical fact multiset and conclusion.
    ordered_filler = filler.replace("These explicit numerical checks", "Explicit numerical checks", 1)
    ordered_filler = ordered_filler.replace("These checks", "Checks", 1)
    ordered = " ".join(part for part in [*ordered_facts, ordered_filler, "Therefore, " + conclusion] if part)
    free_count, ordered_count = len(_words(free)), len(_words(ordered))
    if not (60 <= free_count <= 90):
        raise AssertionError(f"free target has {free_count} words")
    difference = abs(free_count - ordered_count)
    if difference > 6 or difference / max(free_count, ordered_count) > 0.05:
        raise AssertionError((free_count, ordered_count))
    return free, ordered


def _fact(kind: str, value: Any, depends_on: Iterable[str] = ()) -> dict[str, Any]:
    return {"kind": kind, "value": value, "depends_on": list(depends_on)}


def _polynomial(seed: int, split: str, index: int, graph: str, template: str) -> tuple[Any, ...]:
    rng = _stable_rng(seed, split, "polynomial", index)
    bound = 18 if split in {"train", "valid", "paraphrase", "composition"} else 90
    u = rng.randint(-bound, bound)
    d = rng.choice([x for x in range(-12 if bound < 50 else -35, 13 if bound < 50 else 36) if abs(x) >= 2])
    v = u + d
    a_value = rng.randint(-bound * 3, bound * 3)
    exists = graph.endswith("constructive") or (graph.endswith("mixed") and index % 2 == 0) or split == "composition"
    quotient = rng.choice([x for x in range(-12, 13) if x])
    if exists:
        value_difference = d * quotient
    else:
        remainder_seed = rng.randint(1, abs(d) - 1)
        value_difference = d * quotient + remainder_seed
    b_value = a_value + value_difference
    remainder = value_difference % abs(d)
    params = {"u": u, "v": v, "a_value": a_value, "b_value": b_value, "input_difference": d,
              "value_difference": value_difference, "remainder": remainder, "modulus": abs(d),
              "quotient": quotient if exists else None, "exists": exists}
    if template.startswith("para"):
        distractor = abs(u) + abs(v) + 7
        prompt = (f"Someone notes the unrelated number {distractor}. Reverse the two given clauses mentally: an integer polynomial is "
                  f"said to send {v} to {b_value}, while it sends {u} to {a_value}. Decide whether those two values can coexist, "
                  "and give a short checkable argument in ordinary English.")
    elif split == "composition":
        prompt = (f"Decide whether there is an integer-coefficient polynomial P with P({u}) = {a_value} and P({v}) = {b_value}. "
                  "Work in reverse from the proposed value difference, and if it is possible identify the integer slope quotient. "
                  "Give a compact, checkable English argument.")
    else:
        prompt = (f"Can an integer-coefficient polynomial P satisfy P({u}) = {a_value} and P({v}) = {b_value}? "
                  "Use the divisibility relation between input and value differences and explain the decision in ordinary English.")
    facts = [
        _fact("input_difference", d),
        _fact("value_difference", value_difference),
        _fact("divisibility_principle", {"divisor": d}, ["input_difference", "value_difference"]),
        _fact("remainder", {"remainder": remainder, "modulus": abs(d)}, ["input_difference", "value_difference"]),
    ]
    sentences = [
        f"The input difference is {d}.",
        f"The proposed value difference is {value_difference}.",
        "Every integer-coefficient polynomial makes the input difference divide the value difference.",
        f"The proposed value difference leaves remainder {remainder} modulo {abs(d)}.",
    ]
    if exists:
        facts.append(_fact("quotient", quotient, ["input_difference", "value_difference"]))
        sentences.append(f"The quotient is {quotient}.")
    conclusion = {"kind": "polynomial_existence", "value": {"exists": exists},
                  "text": f"Such an integer-coefficient polynomial {'can' if exists else 'cannot'} exist."}
    sentences.append(conclusion["text"])
    return prompt, params, facts, conclusion, *_make_targets(sentences)


def _diophantine(seed: int, split: str, index: int, graph: str, template: str) -> tuple[Any, ...]:
    rng = _stable_rng(seed, split, "diophantine", index)
    bound = 35 if split != "near" else 150
    g = rng.randint(2, 12 if bound < 100 else 30)
    while True:
        pa, pb = rng.randint(2, bound), rng.randint(2, bound)
        if math.gcd(pa, pb) == 1:
            break
    a, b = g * pa, g * pb
    gcd_value, bez_u, bez_v = _extended_gcd(a, b)
    solvable = not graph.endswith("obstruction") and not (graph.endswith("mixed") and index % 2)
    scale = rng.choice([x for x in range(-9, 10) if x])
    c = gcd_value * scale if solvable else gcd_value * scale + rng.randint(1, gcd_value - 1)
    x, y = bez_u * scale, bez_v * scale
    params = {"a": a, "b": b, "c": c, "gcd": gcd_value, "solvable": solvable,
              "bezout_u": bez_u, "bezout_v": bez_v, "solution_x": x if solvable else None,
              "solution_y": y if solvable else None}
    if template.startswith("para"):
        prompt = (f"The letter names are immaterial, and {abs(c)+11} is a distractor. Determine whether integers r and s can make "
                  f"{b} times s plus {a} times r equal {c}. Give every numerical check needed for a compact English proof.")
    elif split == "composition":
        prompt = (f"Starting from the divisibility condition and working toward a witness, decide whether {a}x + {b}y = {c} "
                  "has an integer solution. Include either a scaled Bezout witness or the obstruction in a checkable English plan.")
    else:
        prompt = (f"Does the equation {a}x + {b}y = {c} have an integer solution? Use the greatest common divisor criterion, "
                  "and give a concrete witness when one exists, in ordinary English.")
    facts = [_fact("gcd", gcd_value), _fact("divides", {"gcd": gcd_value, "c": c, "holds": solvable}, ["gcd"])]
    sentences = [f"The greatest common divisor is {gcd_value}.", f"It {'does' if solvable else 'does not'} divide {c}."]
    if solvable:
        facts.extend([
            _fact("bezout", {"u": bez_u, "v": bez_v, "gcd": gcd_value}, ["gcd"]),
            _fact("solution", {"x": x, "y": y, "c": c}, ["bezout", "divides"]),
        ])
        sentences.extend([f"Bezout coefficients are {bez_u} and {bez_v}.", f"A solution is x = {x} and y = {y}."])
    else:
        facts.append(_fact("combination_invariant", {"a": a, "b": b, "gcd": gcd_value}, ["gcd"]))
        sentences.append(f"Every integer combination of {a} and {b} is divisible by {gcd_value}.")
    conclusion = {"kind": "diophantine_solvability", "value": {"solvable": solvable},
                  "text": "An integer solution exists." if solvable else "No integer solution exists."}
    sentences.append(conclusion["text"])
    return prompt, params, facts, conclusion, *_make_targets(sentences)


def _modular(seed: int, split: str, index: int, graph: str, template: str) -> tuple[Any, ...]:
    rng = _stable_rng(seed, split, "modular", index)
    primes = [5, 7, 11, 13, 17, 19] if split != "near" else [23, 29, 31, 37, 41, 43]
    modulus = rng.choice(primes)
    base = rng.randint(2, modulus - 2)
    period = _multiplicative_order(base, modulus)
    selected_class = rng.randrange(period)
    target = pow(base, selected_class, modulus)
    classes = [n for n in range(period) if pow(base, n, modulus) == target]
    task_kind = "prime_filter" if graph.endswith("prime_filter") or split == "composition" else "classes"
    low, high = (2, max(17, period * 5 + 7))
    if split == "near":
        high += 60
    candidates = [n for n in range(low, high + 1) if _is_prime(n)]
    valid = [n for n in candidates if n % period in classes] if task_kind == "prime_filter" else classes
    params = {"base": base, "modulus": modulus, "target_residue": target, "period": period,
              "classes": classes, "range_low": low, "range_high": high, "task_kind": task_kind,
              "prime_candidates": candidates if task_kind == "prime_filter" else [], "valid_exponents": valid}
    if template.startswith("para"):
        prompt = (f"Ignore the unrelated residue {(target+2)%modulus}. Powers of {base} are read modulo {modulus}. "
                  f"Which exponent classes produce residue {target}? State the short cycle and the resulting classes in ordinary English.")
    elif task_kind == "prime_filter":
        prompt = (f"For powers of {base} modulo {modulus}, find all prime exponents from {low} through {high} that give residue {target}. "
                  "First identify the residue period and exponent classes, then filter the bounded prime candidates. Give a checkable English plan.")
    else:
        prompt = (f"For powers of {base} modulo {modulus}, which exponent classes give residue {target}? "
                  "Find the shortest repeating period and report the classes modulo that period in ordinary English.")
    facts = [
        _fact("period", {"base": base, "modulus": modulus, "period": period}),
        _fact("classes", {"classes": classes, "period": period}, ["period"]),
    ]
    sentences = [f"The powers of {base} repeat with period {period} modulo {modulus}.",
                 f"The target residue occurs for exponent classes {_fmt_list(classes)} modulo {period}."]
    if task_kind == "prime_filter":
        facts.extend([
            _fact("prime_candidates", candidates),
            _fact("intersection", valid, ["classes", "prime_candidates"]),
        ])
        sentences.extend([f"The prime candidates in the stated range are {_fmt_list(candidates)}.",
                          f"After intersecting the conditions, the valid exponents are {_fmt_list(valid)}."])
    conclusion = {"kind": "modular_exponents", "value": {"exponents": valid},
                  "text": f"The required exponents are {_fmt_list(valid)}."}
    sentences.append(conclusion["text"])
    return prompt, params, facts, conclusion, *_make_targets(sentences)


def _double_count(seed: int, split: str, index: int, graph: str, template: str) -> tuple[Any, ...]:
    rng = _stable_rng(seed, split, "doublecount", index)
    if split == "composition":
        universe, tuple_length = rng.randint(2, 4), rng.randint(2, 3)
    else:
        while True:
            universe, tuple_length = rng.randint(1, 8), rng.randint(1, 8)
            product = universe * tuple_length
            if product <= 16 and (split != "near" or product >= 12):
                break
    label_start = rng.randint(-5000, -1) if split == "near" else rng.randint(1, 10000)
    label_end = label_start + universe - 1
    tuple_count = 2 ** (universe * tuple_length)
    absent_count = 2 ** (tuple_length * (universe - 1))
    contain_count = tuple_count - absent_count
    composition = split == "composition"
    params = {"universe": universe, "tuple_length": tuple_length, "label_start": label_start,
              "label_end": label_end, "tuple_count": tuple_count,
              "absent_count": absent_count, "contain_count": contain_count, "composition": composition}
    facts = [_fact("tuple_count", tuple_count), _fact("absent_count", absent_count, ["tuple_count"]),
             _fact("contain_count", contain_count, ["tuple_count", "absent_count"])]
    sentences = [f"There are {tuple_count} ordered tuples in total.",
                 f"A fixed element is absent from {absent_count} tuples.",
                 f"So a fixed element occurs in {contain_count} tuples."]
    if composition:
        class_one = rng.randint(1, universe - 1)
        class_two = universe - class_one
        weight_one, weight_two = rng.sample(range(1, 6), 2)
        contribution_one = class_one * weight_one * contain_count
        contribution_two = class_two * weight_two * contain_count
        answer = contribution_one + contribution_two
        params.update({"class_sizes": [class_one, class_two], "class_weights": [weight_one, weight_two],
                       "class_contributions": [contribution_one, contribution_two], "answer": answer})
        facts.extend([
            _fact("class_1_contribution", {"class_id": 1, "size": class_one, "weight": weight_one,
                                            "contain_count": contain_count, "contribution": contribution_one}, ["contain_count"]),
            _fact("class_2_contribution", {"class_id": 2, "size": class_two, "weight": weight_two,
                                            "contain_count": contain_count, "contribution": contribution_two}, ["contain_count"]),
        ])
        sentences.extend([
            f"Class 1 has {class_one} elements of weight {weight_one}, contributing {contribution_one}.",
            f"Class 2 has {class_two} elements of weight {weight_two}, contributing {contribution_two}.",
        ])
        prompt = (f"Consider ordered {tuple_length}-tuples of subsets of the {universe}-element universe numbered from {label_start} through {label_end}. Class 1 has {class_one} elements "
                  f"of weight {weight_one}, and class 2 has {class_two} elements of weight {weight_two}. Find the weighted sum of union "
                  "memberships over every ordered tuple by combining complement counting and the two class contributions. Answer in English.")
        conclusion = {"kind": "double_count_sum", "value": {"sum": answer},
                      "text": f"The weighted sum of the union sizes is {answer}."}
    else:
        answer = universe * contain_count
        params["answer"] = answer
        facts.append(_fact("total_incidences", {"universe": universe, "total": answer}, ["contain_count"]))
        sentences.append(f"Summing over all {universe} elements gives {answer} incidences.")
        if template.startswith("para"):
            prompt = (f"The number {universe+tuple_length+9} is irrelevant. Take an ordered list of {tuple_length} subsets from the universe "
                      f"whose {universe} elements are numbered from {label_start} through {label_end}. Across every possible list, add the size of its union. Compute the total by counting one "
                      "fixed point first, and explain the argument in ordinary English.")
        else:
            prompt = (f"For every ordered {tuple_length}-tuple of subsets of the {universe}-element universe numbered from {label_start} through {label_end}, take the size of the union. "
                      "Find the sum of these union sizes over all tuples by double counting element incidences, and explain it in English.")
        conclusion = {"kind": "double_count_sum", "value": {"sum": answer},
                      "text": f"The sum of the union sizes is {answer}."}
    sentences.append(conclusion["text"])
    return prompt, params, facts, conclusion, *_make_targets(sentences)


def _recurrence_state(params: dict[str, Any], steps: int) -> tuple[int, int]:
    x, y = params["initial_state"]
    for _ in range(steps):
        x, y = y, (x + params["beta"] * y + params["gamma"]) % params["modulus"]
    return x, y


def _recurrence(seed: int, split: str, index: int, graph: str, template: str) -> tuple[Any, ...]:
    rng = _stable_rng(seed, split, "recurrence", index)
    modulus = rng.randint(3, 8 if split != "near" else 13)
    beta, gamma = rng.randint(0, modulus - 1), rng.randint(0, modulus - 1)
    initial = [rng.randrange(modulus), rng.randrange(modulus)]
    transition = {"modulus": modulus, "beta": beta, "gamma": gamma, "initial_state": initial}
    seen: dict[tuple[int, int], int] = {}
    state = tuple(initial)
    step = 0
    while state not in seen:
        seen[state] = step
        state = (state[1], (state[0] + beta * state[1] + gamma) % modulus)
        step += 1
    cycle_start, repeat_step = seen[state], step
    period = repeat_step - cycle_start
    target_index = rng.randint(100, 500 if split != "near" else 5000)
    remainder = (target_index - cycle_start) % period
    reduced = cycle_start + remainder
    target_state = _recurrence_state(transition, reduced)
    start_state = _recurrence_state(transition, cycle_start)
    params = {**transition, "cycle_start": cycle_start, "repeat_step": repeat_step, "period": period,
              "target_index": target_index, "remainder": remainder, "reduced_index": reduced,
              "target_state": list(target_state)}
    if template.startswith("para"):
        prompt = (f"Rename the pair at time n as a pair-state. Begin at ({initial[0]}, {initial[1]}); replace (r, s) by "
                  f"(s, r + {beta} s + {gamma}, reduced modulo {modulus}). The unrelated number {modulus+17} can be ignored. "
                  f"Find the pair-state at time {target_index} using a repeated state, and explain the reduction in English.")
    else:
        prompt = (f"A pair-state recurrence modulo {modulus} starts at ({initial[0]}, {initial[1]}). From (x, y), the next state is "
                  f"(y, x + {beta}y + {gamma}), with both coordinates reduced modulo {modulus}. Find the state at step {target_index} "
                  "by identifying a repeated state and reducing the index. Give a checkable English plan.")
    facts = [
        _fact("state_at", {"step": cycle_start, "x": start_state[0], "y": start_state[1]}),
        _fact("repeat_state", {"step": repeat_step, "x": start_state[0], "y": start_state[1]}, ["state_at"]),
        _fact("period", period, ["state_at", "repeat_state"]),
        _fact("index_reduction", {"index": target_index, "remainder": remainder, "reduced": reduced}, ["period"]),
        _fact("target_state", {"step": reduced, "x": target_state[0], "y": target_state[1]}, ["index_reduction"]),
    ]
    sentences = [
        f"The state at step {cycle_start} is ({start_state[0]}, {start_state[1]}).",
        f"The same state next appears at step {repeat_step}.",
        f"Thus the cycle has period {period}.",
        f"Index {target_index} reduces to step {reduced} because the cycle remainder is {remainder}.",
        f"The state there is ({target_state[0]}, {target_state[1]}).",
    ]
    conclusion = {"kind": "recurrence_state", "value": {"state": [target_state[0], target_state[1]]},
                  "text": f"The required state is ({target_state[0]}, {target_state[1]})."}
    sentences.append(conclusion["text"])
    return prompt, params, facts, conclusion, *_make_targets(sentences)


BUILDERS = {
    "polynomial_value_obstruction": _polynomial,
    "diophantine_solvability": _diophantine,
    "modular_period_prime_filter": _modular,
    "finite_double_count": _double_count,
    "finite_recurrence_period": _recurrence,
}


GRAPH_NAMES = {
    "polynomial_value_obstruction": ("obstruction", "mixed", "constructive"),
    "diophantine_solvability": ("obstruction", "mixed", "constructive"),
    "modular_period_prime_filter": ("classes_a", "prime_filter", "classes_b"),
    "finite_double_count": ("complement_a", "complement_b", "complement_c"),
    "finite_recurrence_period": ("cycle_a", "cycle_b", "cycle_c"),
}


def _graph_and_template(family: str, split: str, index: int) -> tuple[str, str]:
    names = GRAPH_NAMES[family]
    if split == "train":
        graph_index = index // 20
        return f"{family}:base:{names[graph_index]}", f"base-{graph_index}"
    if split == "paraphrase":
        graph_index = index % 3
        return f"{family}:base:{names[graph_index]}", f"para-{index % 4}"
    if split == "composition":
        return f"{family}:composition:reverse-or-combine", f"composition-{index % 4}"
    graph_index = index % 3
    return f"{family}:base:{names[graph_index]}", f"base-{graph_index}"


def _build_instance(seed: int, family: str, split: str, index: int, generation_index: int | None = None) -> Instance:
    graph_id, template_id = _graph_and_template(family, split, index)
    graph_leaf = graph_id.rsplit(":", 1)[-1]
    generation_index = index if generation_index is None else generation_index
    prompt, parameters, facts, conclusion, target_free, target_ordered = BUILDERS[family](
        seed, split, generation_index, graph_leaf, template_id
    )
    parameter_hash = _parameter_hash(parameters)
    semantic_id = f"vpl-v{SCHEMA_VERSION}:{family}:{parameter_hash}"
    instance_hash = hashlib.sha256(f"{split}:{semantic_id}:{graph_id}:{template_id}".encode()).hexdigest()[:10]
    return Instance(
        id=f"vpl-v{SCHEMA_VERSION}-{split}-{family}-{index:03d}-{instance_hash}", family=family, split=split,
        semantic_instance_id=semantic_id, parameter_hash=parameter_hash, graph_id=graph_id,
        prompt_template_id=template_id, prompt=prompt,
        target_free=target_free, target_ordered=target_ordered, parameters=parameters,
        required_facts=facts, conclusion=conclusion,
    )


def generate_instances(seed: int = DEFAULT_SEED) -> list[Instance]:
    generated: list[Instance] = []
    train_by_family: dict[str, list[Instance]] = {}
    used_semantics: set[str] = set()

    def unique_instance(family: str, split: str, index: int) -> Instance:
        for attempt in range(1000):
            candidate = _build_instance(seed, family, split, index, index + attempt * 10007)
            if candidate.semantic_instance_id not in used_semantics:
                used_semantics.add(candidate.semantic_instance_id)
                return candidate
        raise RuntimeError(f"could not produce unique semantics for {family}/{split}/{index}")

    for family in FAMILIES:
        train = [unique_instance(family, "train", index) for index in range(SPLIT_COUNTS["train"])]
        train_by_family[family] = train
        generated.extend(train)
        for split in ("valid", "near", "paraphrase", "composition"):
            generated.extend(unique_instance(family, split, index) for index in range(SPLIT_COUNTS[split]))
        # Train-fit is a deterministic exact sample of training semantics and text.
        picks = _stable_rng(seed, family, "train_fit").sample(range(len(train)), SPLIT_COUNTS["train_fit"])
        for out_index, source_index in enumerate(sorted(picks)):
            source = train[source_index]
            generated.append(Instance(
                id=f"vpl-v{SCHEMA_VERSION}-train_fit-{family}-{out_index:03d}-{source.id[-10:]}", family=family,
                split="train_fit", semantic_instance_id=source.semantic_instance_id, parameter_hash=source.parameter_hash,
                graph_id=source.graph_id,
                prompt_template_id=source.prompt_template_id, prompt=source.prompt, target_free=source.target_free,
                target_ordered=source.target_ordered, parameters=source.parameters, required_facts=source.required_facts,
                conclusion=source.conclusion,
            ))
    split_order = {name: index for index, name in enumerate(SPLIT_COUNTS)}
    return sorted(generated, key=lambda row: (split_order[row.split], FAMILIES.index(row.family), row.id))


CONNECTOR = r"(?:First|Next|Then|Finally|Therefore),\s*"
INT = r"([+-]?\d+)"
LIST = r"(none|[+-]?\d+(?:\s*(?:,|and)\s*[+-]?\d+)*)"


def _compile(pattern: str) -> re.Pattern[str]:
    return re.compile(rf"(?:{CONNECTOR})?{pattern}", re.IGNORECASE)


PATTERNS: dict[str, list[tuple[str, re.Pattern[str], Any]]] = {
    "polynomial_value_obstruction": [
        ("input_difference", _compile(rf"The input difference is {INT}\."), lambda m: int(m.group(1))),
        ("value_difference", _compile(rf"The proposed value difference is {INT}\."), lambda m: int(m.group(1))),
        ("divisibility_principle", _compile(r"Every integer-coefficient polynomial makes the input difference divide the value difference\."), lambda m: None),
        ("remainder", _compile(rf"The proposed value difference leaves remainder {INT} modulo {INT}\."), lambda m: {"remainder": int(m.group(1)), "modulus": int(m.group(2))}),
        ("quotient", _compile(rf"The quotient is {INT}\."), lambda m: int(m.group(1))),
        ("conclusion", _compile(r"Such an integer-coefficient polynomial (can|cannot) exist\."), lambda m: {"exists": m.group(1).lower() == "can"}),
    ],
    "diophantine_solvability": [
        ("gcd", _compile(rf"The greatest common divisor is {INT}\."), lambda m: int(m.group(1))),
        ("divides", _compile(rf"It (does|does not) divide {INT}\."), lambda m: {"holds": m.group(1).lower() == "does", "c": int(m.group(2))}),
        ("combination_invariant", _compile(rf"Every integer combination of {INT} and {INT} is divisible by {INT}\."), lambda m: {"a": int(m.group(1)), "b": int(m.group(2)), "gcd": int(m.group(3))}),
        ("bezout", _compile(rf"Bezout coefficients are {INT} and {INT}\."), lambda m: {"u": int(m.group(1)), "v": int(m.group(2))}),
        ("solution", _compile(rf"A solution is x = {INT} and y = {INT}\."), lambda m: {"x": int(m.group(1)), "y": int(m.group(2))}),
        ("conclusion", _compile(r"(An integer solution exists|No integer solution exists)\."), lambda m: {"solvable": m.group(1).lower().startswith("an")}),
    ],
    "modular_period_prime_filter": [
        ("period", _compile(rf"The powers of {INT} repeat with period {INT} modulo {INT}\."), lambda m: {"base": int(m.group(1)), "period": int(m.group(2)), "modulus": int(m.group(3))}),
        ("classes", _compile(rf"The target residue occurs for exponent classes {LIST} modulo {INT}\."), lambda m: {"classes": _parse_list(m.group(1)), "period": int(m.group(2))}),
        ("prime_candidates", _compile(rf"The prime candidates in the stated range are {LIST}\."), lambda m: _parse_list(m.group(1))),
        ("intersection", _compile(rf"After intersecting the conditions, the valid exponents are {LIST}\."), lambda m: _parse_list(m.group(1))),
        ("conclusion", _compile(rf"The required exponents are {LIST}\."), lambda m: {"exponents": _parse_list(m.group(1))}),
    ],
    "finite_double_count": [
        ("tuple_count", _compile(rf"There are {INT} ordered tuples in total\."), lambda m: int(m.group(1))),
        ("absent_count", _compile(rf"A fixed element is absent from {INT} tuples\."), lambda m: int(m.group(1))),
        ("contain_count", _compile(rf"So a fixed element occurs in {INT} tuples\."), lambda m: int(m.group(1))),
        ("total_incidences", _compile(rf"Summing over all {INT} elements gives {INT} incidences\."), lambda m: {"universe": int(m.group(1)), "total": int(m.group(2))}),
        ("class_contribution", _compile(rf"Class {INT} has {INT} elements of weight {INT}, contributing {INT}\."), lambda m: {"class_id": int(m.group(1)), "size": int(m.group(2)), "weight": int(m.group(3)), "contribution": int(m.group(4))}),
        ("conclusion", _compile(rf"The (weighted sum|sum) of the union sizes is {INT}\."), lambda m: {"sum": int(m.group(2))}),
    ],
    "finite_recurrence_period": [
        ("state_at", _compile(rf"The state at step {INT} is \({INT}, {INT}\)\."), lambda m: {"step": int(m.group(1)), "x": int(m.group(2)), "y": int(m.group(3))}),
        ("repeat_state", _compile(rf"The same state next appears at step {INT}\."), lambda m: {"step": int(m.group(1))}),
        ("period", _compile(rf"Thus the cycle has period {INT}\."), lambda m: int(m.group(1))),
        ("index_reduction", _compile(rf"Index {INT} reduces to step {INT} because the cycle remainder is {INT}\."), lambda m: {"index": int(m.group(1)), "reduced": int(m.group(2)), "remainder": int(m.group(3))}),
        ("target_state", _compile(rf"The state there is \({INT}, {INT}\)\."), lambda m: {"x": int(m.group(1)), "y": int(m.group(2))}),
        ("conclusion", _compile(rf"The required state is \({INT}, {INT}\)\."), lambda m: {"state": [int(m.group(1)), int(m.group(2))]}),
    ],
}


def _parse_list(text: str) -> list[int]:
    if text.strip().lower() == "none":
        return []
    return sorted(set(map(int, re.findall(r"[+-]?\d+", text))))


def _enrich_claim(instance: Instance, kind: str, value: Any) -> tuple[str, Any]:
    p = instance.parameters
    if kind == "divisibility_principle":
        value = {"divisor": p["input_difference"]}
    elif instance.family == "diophantine_solvability":
        if kind == "divides":
            value["gcd"] = p["gcd"]
        elif kind == "bezout":
            value["gcd"] = p["gcd"]
        elif kind == "solution":
            value["c"] = p["c"]
    elif instance.family == "finite_double_count" and kind == "class_contribution":
        kind = f"class_{value['class_id']}_contribution"
        value["contain_count"] = p["contain_count"]
    elif instance.family == "finite_recurrence_period":
        if kind == "repeat_state":
            cycle_state = _recurrence_state(p, p["cycle_start"])
            value.update({"x": cycle_state[0], "y": cycle_state[1]})
        elif kind == "target_state":
            value["step"] = p["reduced_index"]
    return kind, value


def parse_response(instance: Instance, response: str) -> dict[str, Any]:
    claims: list[dict[str, Any]] = []
    errors: list[str] = []
    for family, patterns in PATTERNS.items():
        for kind, pattern, converter in patterns:
            for match in pattern.finditer(response):
                parsed_kind, value = _enrich_claim(instance, kind, converter(match))
                claims.append({"kind": parsed_kind, "value": value, "position": match.start(), "source_family": family})
    own = [claim for claim in claims if claim["source_family"] == instance.family]
    foreign = [claim for claim in claims if claim["source_family"] != instance.family]
    if foreign:
        errors.append("unexpected family-specific claim")
    conclusions = [claim for claim in own if claim["kind"] == "conclusion"]
    if len(conclusions) != 1:
        errors.append("expected exactly one conclusion")
    critical = [claim for claim in own if claim["kind"] != "conclusion"]
    expected_kinds = {fact["kind"] for fact in instance.required_facts}
    for claim in critical:
        if claim["kind"] not in expected_kinds:
            errors.append(f"unexpected claim {claim['kind']}")
    by_kind: dict[str, list[dict[str, Any]]] = {}
    for claim in critical:
        by_kind.setdefault(claim["kind"], []).append(claim)
    for kind in expected_kinds:
        values = by_kind.get(kind, [])
        if not values:
            errors.append(f"missing claim {kind}")
        elif len({json.dumps(row["value"], sort_keys=True) for row in values}) > 1:
            errors.append(f"contradictory duplicate {kind}")
        elif len(values) > 1:
            errors.append(f"duplicate claim {kind}")
    return {"parse_valid": not errors, "errors": sorted(set(errors)), "claims": own}


def _correct_claims(instance: Instance, claims: list[dict[str, Any]]) -> tuple[int, int, int]:
    expected = {(fact["kind"], json.dumps(fact["value"], sort_keys=True)) for fact in instance.required_facts}
    parsed = {(claim["kind"], json.dumps(claim["value"], sort_keys=True)) for claim in claims if claim["kind"] != "conclusion"}
    return len(expected & parsed), len(parsed), len(expected)


def _order_valid(instance: Instance, claims: list[dict[str, Any]]) -> bool:
    position = {claim["kind"]: claim["position"] for claim in claims if claim["kind"] != "conclusion"}
    for fact in instance.required_facts:
        if fact["kind"] not in position:
            return False
        if any(dependency not in position or position[dependency] >= position[fact["kind"]] for dependency in fact["depends_on"]):
            return False
    return True


def evaluate_response(instance: Instance, response: str, condition: str) -> dict[str, Any]:
    if condition not in {"free", "ordered"}:
        raise ValueError("condition must be free or ordered")
    parsed = parse_response(instance, response)
    claims = parsed["claims"]
    correct, parsed_count, expected_count = _correct_claims(instance, claims)
    conclusion_claims = [claim for claim in claims if claim["kind"] == "conclusion"]
    conclusion_correct = len(conclusion_claims) == 1 and conclusion_claims[0]["value"] == instance.conclusion["value"]
    order_valid = _order_valid(instance, claims) if condition == "ordered" else True
    precision = correct / parsed_count if parsed_count else 0.0
    recall = correct / expected_count if expected_count else 1.0
    private_math_valid = verify_private_math(instance)
    strict = (parsed["parse_valid"] and private_math_valid and precision == 1.0 and recall == 1.0
              and conclusion_correct and order_valid)
    return {
        "id": instance.id, "split": instance.split, "family": instance.family, "condition": condition,
        "response": response, "parse_valid": parsed["parse_valid"], "parse_errors": parsed["errors"],
        "parsed_claims": [{key: value for key, value in claim.items() if key != "source_family"} for claim in claims],
        "required_fact_precision": precision, "required_fact_recall": recall, "order_valid": order_valid,
        "conclusion_correct": conclusion_correct, "python_strict": strict,
        "private_math_valid": private_math_valid,
    }


def verify_private_math(instance: Instance) -> bool:
    """Recompute every private oracle value instead of trusting generated labels."""
    p = instance.parameters
    facts = {fact["kind"]: fact["value"] for fact in instance.required_facts}
    if instance.family == "polynomial_value_obstruction":
        d, e = p["v"] - p["u"], p["b_value"] - p["a_value"]
        remainder = e % abs(d)
        expected = (facts["input_difference"] == d and facts["value_difference"] == e
                    and facts["divisibility_principle"] == {"divisor": d}
                    and facts["remainder"] == {"remainder": remainder, "modulus": abs(d)}
                    and instance.conclusion["value"] == {"exists": remainder == 0})
        return expected and ("quotient" not in facts or facts["quotient"] == e // d)
    if instance.family == "diophantine_solvability":
        g = math.gcd(p["a"], p["b"])
        solvable = p["c"] % g == 0
        if facts.get("gcd") != g or facts.get("divides") != {"gcd": g, "c": p["c"], "holds": solvable}:
            return False
        if instance.conclusion["value"] != {"solvable": solvable}:
            return False
        if solvable:
            bezout, solution = facts.get("bezout", {}), facts.get("solution", {})
            return (p["a"] * bezout.get("u", 0) + p["b"] * bezout.get("v", 0) == g
                    and bezout.get("gcd") == g
                    and p["a"] * solution.get("x", 0) + p["b"] * solution.get("y", 0) == p["c"]
                    and solution.get("c") == p["c"])
        return facts.get("combination_invariant") == {"a": p["a"], "b": p["b"], "gcd": g}
    if instance.family == "modular_period_prime_filter":
        period = _multiplicative_order(p["base"], p["modulus"])
        classes = [n for n in range(period) if pow(p["base"], n, p["modulus"]) == p["target_residue"]]
        if facts.get("period") != {"base": p["base"], "modulus": p["modulus"], "period": period}:
            return False
        if facts.get("classes") != {"classes": classes, "period": period}:
            return False
        if p["task_kind"] == "prime_filter":
            candidates = [n for n in range(p["range_low"], p["range_high"] + 1) if _is_prime(n)]
            valid = [n for n in candidates if n % period in classes]
            return (facts.get("prime_candidates") == candidates and facts.get("intersection") == valid
                    and instance.conclusion["value"] == {"exponents": valid})
        return instance.conclusion["value"] == {"exponents": classes}
    if instance.family == "finite_double_count":
        total = 2 ** (p["universe"] * p["tuple_length"])
        absent = 2 ** (p["tuple_length"] * (p["universe"] - 1))
        contain = total - absent
        if (facts.get("tuple_count"), facts.get("absent_count"), facts.get("contain_count")) != (total, absent, contain):
            return False
        if p["composition"]:
            contribution_sum = 0
            for class_id in (1, 2):
                value = facts.get(f"class_{class_id}_contribution", {})
                if value.get("class_id") != class_id or value.get("contain_count") != contain:
                    return False
                contribution = value.get("size", 0) * value.get("weight", 0) * contain
                if value.get("contribution") != contribution:
                    return False
                contribution_sum += contribution
            return instance.conclusion["value"] == {"sum": contribution_sum}
        answer = p["universe"] * contain
        return facts.get("total_incidences") == {"universe": p["universe"], "total": answer} and instance.conclusion["value"] == {"sum": answer}
    seen: dict[tuple[int, int], int] = {}
    state = tuple(p["initial_state"])
    step = 0
    while state not in seen:
        seen[state] = step
        state = (state[1], (state[0] + p["beta"] * state[1] + p["gamma"]) % p["modulus"])
        step += 1
    cycle_start, repeat_step = seen[state], step
    period = repeat_step - cycle_start
    remainder = (p["target_index"] - cycle_start) % period
    reduced = cycle_start + remainder
    start_state, target_state = _recurrence_state(p, cycle_start), _recurrence_state(p, reduced)
    return (
        facts.get("state_at") == {"step": cycle_start, "x": start_state[0], "y": start_state[1]}
        and facts.get("repeat_state") == {"step": repeat_step, "x": start_state[0], "y": start_state[1]}
        and facts.get("period") == period
        and facts.get("index_reduction") == {"index": p["target_index"], "remainder": remainder, "reduced": reduced}
        and facts.get("target_state") == {"step": reduced, "x": target_state[0], "y": target_state[1]}
        and instance.conclusion["value"] == {"state": list(target_state)}
    )


def oracle_response(instance: Instance, condition: str) -> str:
    return instance.target_free if condition == "free" else instance.target_ordered


def _mutate(value: Any) -> Any:
    if isinstance(value, bool):
        return not value
    if isinstance(value, int):
        return value + 1
    if isinstance(value, list):
        return [*value, (max(value) + 1 if value else 1)]
    if isinstance(value, dict):
        changed = dict(value)
        for key in reversed(list(changed)):
            if isinstance(changed[key], (int, bool)):
                changed[key] = _mutate(changed[key])
                return changed
            if isinstance(changed[key], list):
                changed[key] = _mutate(changed[key])
                return changed
    raise ValueError(f"cannot mutate {value!r}")


def one_fact_mutant(instance: Instance, condition: str = "ordered") -> str:
    """Mutate exactly one canonical fact sentence while retaining valid English grammar."""
    response = oracle_response(instance, condition)
    # The first DAG node is always a rendered numerical claim. Keeping the
    # negative control at a root also guarantees that exactly one extracted
    # fact changes rather than silently changing an enriched private field.
    fact = instance.required_facts[0]
    expected_json = json.dumps(fact["value"], sort_keys=True)
    parsed = parse_response(instance, response)
    claim = next(row for row in parsed["claims"] if row["kind"] == fact["kind"])
    mutated = _mutate(claim["value"])
    start = claim["position"]
    # Re-render the entire target from its parsed claims, changing only the chosen fact.
    rendered = render_claims(instance, parsed["claims"], condition, override=(fact["kind"], mutated))
    reparsed = parse_response(instance, rendered)
    changed_claim = next(row for row in reparsed["claims"] if row["kind"] == fact["kind"])
    assert json.dumps(changed_claim["value"], sort_keys=True) != expected_json and start >= 0
    return rendered


def render_claims(instance: Instance, claims: list[dict[str, Any]], condition: str, override: tuple[str, Any] | None = None) -> str:
    values = {claim["kind"]: claim["value"] for claim in claims}
    if override:
        values[override[0]] = override[1]
    p = instance.parameters
    family = instance.family
    s: list[str]
    if family == "polynomial_value_obstruction":
        s = [f"The input difference is {values['input_difference']}.", f"The proposed value difference is {values['value_difference']}.",
             "Every integer-coefficient polynomial makes the input difference divide the value difference.",
             f"The proposed value difference leaves remainder {values['remainder']['remainder']} modulo {values['remainder']['modulus']}."]
        if "quotient" in values: s.append(f"The quotient is {values['quotient']}.")
        s.append(f"Such an integer-coefficient polynomial {'can' if values['conclusion']['exists'] else 'cannot'} exist.")
    elif family == "diophantine_solvability":
        s = [f"The greatest common divisor is {values['gcd']}.", f"It {'does' if values['divides']['holds'] else 'does not'} divide {values['divides']['c']}."]
        if "combination_invariant" in values:
            v = values["combination_invariant"]; s.append(f"Every integer combination of {v['a']} and {v['b']} is divisible by {v['gcd']}.")
        else:
            v = values["bezout"]; s.append(f"Bezout coefficients are {v['u']} and {v['v']}.")
            v = values["solution"]; s.append(f"A solution is x = {v['x']} and y = {v['y']}.")
        s.append("An integer solution exists." if values["conclusion"]["solvable"] else "No integer solution exists.")
    elif family == "modular_period_prime_filter":
        v = values["period"]; s = [f"The powers of {v['base']} repeat with period {v['period']} modulo {v['modulus']}."]
        v = values["classes"]; s.append(f"The target residue occurs for exponent classes {_fmt_list(v['classes'])} modulo {v['period']}.")
        if "prime_candidates" in values:
            s.extend([f"The prime candidates in the stated range are {_fmt_list(values['prime_candidates'])}.",
                      f"After intersecting the conditions, the valid exponents are {_fmt_list(values['intersection'])}."])
        s.append(f"The required exponents are {_fmt_list(values['conclusion']['exponents'])}.")
    elif family == "finite_double_count":
        s = [f"There are {values['tuple_count']} ordered tuples in total.", f"A fixed element is absent from {values['absent_count']} tuples.",
             f"So a fixed element occurs in {values['contain_count']} tuples."]
        if "total_incidences" in values:
            v = values["total_incidences"]; s.append(f"Summing over all {v['universe']} elements gives {v['total']} incidences.")
        else:
            for kind in ("class_1_contribution", "class_2_contribution"):
                v = values[kind]; s.append(f"Class {v['class_id']} has {v['size']} elements of weight {v['weight']}, contributing {v['contribution']}.")
        prefix = "weighted sum" if p["composition"] else "sum"
        s.append(f"The {prefix} of the union sizes is {values['conclusion']['sum']}.")
    else:
        v = values["state_at"]; s = [f"The state at step {v['step']} is ({v['x']}, {v['y']})."]
        v = values["repeat_state"]; s.append(f"The same state next appears at step {v['step']}.")
        s.append(f"Thus the cycle has period {values['period']}.")
        v = values["index_reduction"]; s.append(f"Index {v['index']} reduces to step {v['reduced']} because the cycle remainder is {v['remainder']}.")
        v = values["target_state"]; s.append(f"The state there is ({v['x']}, {v['y']}).")
        v = values["conclusion"]["state"]; s.append(f"The required state is ({v[0]}, {v[1]}).")
    free, ordered = _make_targets(s)
    return free if condition == "free" else ordered


def write_jsonl(path: Path, rows: Iterable[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")


def load_instances(split: str, data_dir: Path = DATA) -> list[Instance]:
    public = {row["id"]: row for row in _read_jsonl(data_dir / f"{split}.prompts.jsonl")}
    targets = {row["id"]: row for row in _read_jsonl(data_dir / f"{split}.targets.jsonl")}
    private = {row["id"]: row for row in _read_jsonl(data_dir / f"{split}.verifier.jsonl")}
    if public.keys() != targets.keys() or public.keys() != private.keys():
        raise ValueError("public, target, and verifier IDs differ")
    return [Instance(id=row["id"], family=row["family"], split=row["split"], semantic_instance_id=row["semantic_instance_id"],
                     parameter_hash=row["parameter_hash"],
                     graph_id=row["graph_id"], prompt_template_id=row["prompt_template_id"], prompt=row["prompt"],
                     target_free=targets[row["id"]]["target_free"], target_ordered=targets[row["id"]]["target_ordered"],
                     parameters=private[row["id"]]["parameters"], required_facts=private[row["id"]]["required_facts"],
                     conclusion=private[row["id"]]["conclusion"]) for row in public.values()]


def _read_jsonl(path: Path) -> list[dict[str, Any]]:
    with path.open(encoding="utf-8") as handle:
        return [json.loads(line) for line in handle if line.strip()]
