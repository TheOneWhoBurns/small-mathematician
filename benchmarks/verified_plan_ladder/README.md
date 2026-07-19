# Verified-plan capability ladder

This benchmark asks a very small model for a compact mathematical plan in ordinary English. A strict family-specific parser extracts every critical claim, a private proof DAG checks the claims and their dependencies, and a separate Lean layer can certify the parsed arithmetic. The model never sees Lean, tactic syntax, theorem names, proof states, or a machine-oriented output language. JSONL is transport only.

The research question is:

> How much mathematical problem-solving ability can be compressed into a very small, memory- and time-efficient, natural-language-only model when formalization, theorem retrieval, and Lean verification are delegated to a fixed external system?

## Families and splits

The five families isolate reusable proof moves:

- `polynomial_value_obstruction`: use `(v-u) | (P(v)-P(u))` to accept or rule out proposed values;
- `diophantine_solvability`: use a gcd obstruction or scale a Bezout witness for `ax+by=c`;
- `modular_period_prime_filter`: find a short residue period, then optionally intersect with bounded prime candidates;
- `finite_double_count`: count total, avoiding, containing, and per-element incidences;
- `finite_recurrence_period`: find a repeated pair-state, its period, reduce a large index, and read the target state.

Each family has 60 training examples from three base proof DAGs. Validation and `train_fit` contain 10 per family. Near, paraphrase, and composition each contain 16 per family. `train_fit` is an explicit sample of training rows. All other parameter hashes are disjoint from training. Near keeps the base graphs and prompt surfaces but changes parameter ranges; paraphrase uses four unseen prompt templates with clause reversal, renaming, and one benign distractor; composition uses a held-out reverse-or-combine graph.

## Boundary and schemas

Only `data/*.prompts.jsonl` is input data. A runner sends only each row's `prompt` string. `data/*.targets.jsonl` contains paired post-training or reference targets and must be withheld during evaluation. `data/*.verifier.jsonl` contains private parameters, required facts, DAG dependencies, and conclusions. `data/*.mutants.jsonl` contains one-fact negative controls.

Predictions are ordinary English transported as JSONL:

```json
{"id":"vpl-v1-...","response":"First, the input difference is 4. ... Therefore, such an integer-coefficient polynomial cannot exist."}
```

Every prompt has two matched targets with the same required fact multiset and conclusion. `target_free` is a 60–90 word unnumbered paragraph. `target_ordered` makes the proof order explicit with `First`, `Next`, and `Therefore`. Pairwise word counts differ by at most six and at most 5%; aggregate word counts differ by at most 5%. The self-test records these values. The tokenizer-specific matched-token check belongs in the training-view preflight because this benchmark intentionally does not depend on a model tokenizer.

## Strict parsing and metrics

The parsers extract all canonical English fact matches, never merely the last match. They reject missing facts, contradictory or repeated fields, more than one conclusion, claims belonging to another family, unexpected claims within a family, and duplicate composition class identifiers. A wrong but well-formed numerical fact remains parseable and then fails mathematical strictness, which lets fact precision and recall diagnose the failure.

`evaluate.py` reports parse rate, critical-fact precision, required-fact recall, order validity, conclusion accuracy, and strict plan rate overall, by family, and for a selected split. Free evaluation ignores ordering; ordered evaluation requires every `depends_on` edge to point forward. Lean-certified strict is added by the sibling certificate emitter rather than duplicated here.

## Generate and verify

From this directory:

```sh
uv run --project ../.. python generate.py
uv run --project ../.. python self_test.py
uv run --project ../.. python evaluate.py --split near --condition ordered --predictions predictions.jsonl
```

The hard preflight is 100% oracle acceptance, 100% rejection of one-fact mutants, zero unintended leakage, and the representation-length constraints. Do not tune on the composition split.

Suggested experimental gates are: at step 100, parse rate at least 90%, train-fit strict at least 70%, and fact precision at least 90%; at step 300, train-fit at least 90%, near at least 70% with every family at least 50%, paraphrase at least 55% and at least 75% of near, composition at least 35% with every family at least 20%, fact precision at least 98%, and exact agreement between Python strict and Lean-certified strict. A representation winner needs at least a 10-point paired advantage on paraphrase or composition, near within five points, and no precision or retention loss; under five points is inconclusive.

