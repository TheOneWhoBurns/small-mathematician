#!/usr/bin/env python3
"""Preflight: determinism, leakage, oracle acceptance, and one-fact rejection."""

from __future__ import annotations

import json
from collections import Counter, defaultdict
from pathlib import Path

from transformers import AutoTokenizer

from benchmark import EVAL_SPLITS, FAMILIES, SPLIT_COUNTS, evaluate_response, generate_instances, one_fact_mutant, oracle_response, parse_response, verify_private_math, _words


def main() -> None:
    first, second = generate_instances(), generate_instances()
    assert [row.public() for row in first] == [row.public() for row in second]
    assert [row.private() for row in first] == [row.private() for row in second]
    assert len({row.id for row in first}) == len(first)

    counts = Counter((row.split, row.family) for row in first)
    for split, count in SPLIT_COUNTS.items():
        for family in FAMILIES:
            assert counts[split, family] == count, (split, family, counts[split, family])

    by_split: dict[str, list] = defaultdict(list)
    for row in first:
        assert verify_private_math(row), row.id
        by_split[row.split].append(row)
    train_semantics = {row.semantic_instance_id for row in by_split["train"]}
    train_parameters = {(row.family, row.parameter_hash) for row in by_split["train"]}
    fit_semantics = {row.semantic_instance_id for row in by_split["train_fit"]}
    assert fit_semantics <= train_semantics
    for split in ("valid", "near", "paraphrase", "composition"):
        assert not (train_semantics & {row.semantic_instance_id for row in by_split[split]}), split
        assert not (train_parameters & {(row.family, row.parameter_hash) for row in by_split[split]}), split
    base_graphs = {row.graph_id for row in by_split["train"]}
    assert all(row.graph_id in base_graphs for row in by_split["near"] + by_split["paraphrase"] + by_split["valid"])
    assert not (base_graphs & {row.graph_id for row in by_split["composition"]})
    base_templates = {row.prompt_template_id for row in by_split["train"]}
    assert not (base_templates & {row.prompt_template_id for row in by_split["paraphrase"]})
    for family in FAMILIES:
        family_train = [row for row in by_split["train"] if row.family == family]
        assert sorted(Counter(row.graph_id for row in family_train).values()) == [20, 20, 20]
        family_para = [row for row in by_split["paraphrase"] if row.family == family]
        assert sorted(Counter(row.prompt_template_id for row in family_para).values()) == [4, 4, 4, 4]

    oracle = []
    mutants = []
    free_words = ordered_words = 0
    max_pair_delta = max_pair_ratio = 0.0
    for row in first:
        for condition in ("free", "ordered"):
            result = evaluate_response(row, oracle_response(row, condition), condition)
            assert result["python_strict"], (row.id, condition, result)
            oracle.append(result)
        free_count, ordered_count = len(_words(row.target_free)), len(_words(row.target_ordered))
        assert 60 <= free_count <= 90
        delta = abs(free_count - ordered_count)
        ratio = delta / max(free_count, ordered_count)
        assert delta <= 6 and ratio <= 0.05
        free_words += free_count
        ordered_words += ordered_count
        max_pair_delta = max(max_pair_delta, delta)
        max_pair_ratio = max(max_pair_ratio, ratio)
        mutant = one_fact_mutant(row, "ordered")
        mutant_parse = parse_response(row, mutant)
        mutant_result = evaluate_response(row, mutant, "ordered")
        assert mutant_parse["parse_valid"], (row.id, mutant_parse)
        assert not mutant_result["python_strict"], (row.id, mutant_result)
        assert mutant_result["required_fact_recall"] < 1.0 or mutant_result["required_fact_precision"] < 1.0
        mutants.append(mutant_result)
    # Structural parser failures are distinct from well-formed wrong facts.
    sample = first[0]
    assert not parse_response(sample, sample.target_ordered + " " + sample.conclusion["text"])["parse_valid"]
    first_sentence = sample.target_ordered.split(".", 1)[0] + "."
    assert not parse_response(sample, first_sentence + " " + sample.target_ordered)["parse_valid"]
    foreign = next(row for row in first if row.family != sample.family)
    assert not parse_response(sample, sample.target_ordered + " " + foreign.target_ordered)["parse_valid"]
    aggregate_ratio = abs(free_words - ordered_words) / max(free_words, ordered_words)
    assert aggregate_ratio <= 0.05

    tokenizer_path = Path(__file__).resolve().parents[2] / "assets" / "models" / "qwen3-0.6b-base"
    tokenizer = AutoTokenizer.from_pretrained(tokenizer_path, local_files_only=True)
    token_pairs = [
        (
            len(tokenizer.encode(row.target_free, add_special_tokens=False)),
            len(tokenizer.encode(row.target_ordered, add_special_tokens=False)),
            row,
        )
        for row in first
    ]
    max_token_ratio = max(abs(a - b) / max(a, b) for a, b, _ in token_pairs)
    assert max_token_ratio <= 0.08
    train_token_pairs = [(a, b) for a, b, row in token_pairs if row.split == "train"]
    train_free_tokens = sum(a for a, _ in train_token_pairs)
    train_ordered_tokens = sum(b for _, b in train_token_pairs)
    aggregate_training_token_ratio = abs(train_free_tokens - train_ordered_tokens) / max(train_free_tokens, train_ordered_tokens)
    assert aggregate_training_token_ratio <= 0.05

    print(json.dumps({
        "status": "PASS",
        "instances": len(first),
        "oracle_responses": len(oracle),
        "oracle_strict_acceptance": sum(row["python_strict"] for row in oracle) / len(oracle),
        "one_fact_mutants": len(mutants),
        "one_fact_mutant_rejection": sum(not row["python_strict"] for row in mutants) / len(mutants),
        "split_totals": {split: len(by_split[split]) for split in SPLIT_COUNTS},
        "max_matched_word_delta": max_pair_delta,
        "max_matched_word_ratio": max_pair_ratio,
        "aggregate_word_ratio": aggregate_ratio,
        "qwen_tokenizer": {
            "path": str(tokenizer_path),
            "max_pair_ratio": max_token_ratio,
            "training_free_tokens": train_free_tokens,
            "training_ordered_tokens": train_ordered_tokens,
            "aggregate_training_ratio": aggregate_training_token_ratio,
        },
        "leakage": {"train_fit_is_train_subset": True, "all_other_semantic_overlap": 0,
                    "paraphrase_prompt_template_overlap": 0, "composition_graph_overlap": 0},
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
