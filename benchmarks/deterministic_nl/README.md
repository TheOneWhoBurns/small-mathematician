# Deterministic natural-language reasoning benchmark

This benchmark measures one narrow part of the project’s research question:

> How much mathematical problem-solving ability can be compressed into a natural-language-only model when formalization, theorem retrieval, and verification are delegated to a fixed external system?

It tests whether the small model can compute and construct correct mathematical
answers, rather than whether it can imitate the wording of a reference proof.
Every model-facing prompt is ordinary mathematical English. The model is never
shown formal prover source, tactic names, proof states, library identifiers, or
the private verifier record.

## What it tests

The development and test splits share five families:

- parenthesized integer calculations;
- greatest common divisors with checkable Bezout coefficients;
- modular inverses;
- integer roots of monic quadratics;
- uniquely solvable two-variable linear systems.

The test split uses larger values and more difficult ranges. It also adds two
families absent from development: simultaneous remainder constraints and the
remainder of a cubic polynomial divided by a linear polynomial. This makes the
benchmark contain both held-out parameter ranges and a modest held-out-family
generalization check.

The default frozen generation has 60 development prompts and 140 test prompts.
The seed, counts, family distribution, and content hashes are in
`data/manifest.json`.

## Boundary and files

`data/*.prompts.jsonl` is the only model-facing data. Each row contains an ID,
split, family label, and natural-language prompt. A runner should send only the
`prompt` value to the model.

`data/*.verifier.jsonl` contains exact answers and verifier parameters. Keep it
outside the model context. It exists locally so results remain reproducible and
cheap to evaluate. There is no downstream formal-prover dependency in version 1.

Predictions use one JSONL transport record per instance:

```json
{"id":"...","response":"I substituted the values and checked the result. The answer is 42."}
```

JSONL is only the evaluation transport. The response itself is natural language.
Prompts request a short final sentence whose family-specific fields can be parsed
without asking the model to emit a programming language.

## Generate, test, and evaluate

From this directory:

```sh
uv run --project ../.. python generate.py
uv run --project ../.. python self_test.py
uv run --project ../.. python evaluate.py --split dev --predictions predictions.jsonl
```

Use `--details-out details.jsonl` to retain per-instance results. The report gives
format validity, exact answer accuracy, a weak reasoning-presence diagnostic,
certificate validity where applicable, and strict pass rate overall and per
family. A missing prediction is scored as a failure.

## Metrics

`answer_accuracy` is exact and programmatically checked. `certificate_valid_rate`
checks mathematical witnesses for Bezout identities, modular inverses, roots,
linear systems, and simultaneous remainder constraints. It accepts any valid
witness, not just the generator’s canonical one.

`reasoning_present_rate` only checks that some prose precedes the final parsed
sentence. It does not claim to judge the correctness or quality of that prose.
`strict_pass_rate` requires a parseable final sentence, exact correctness, all
applicable certificate checks, and at least four words outside the final sentence.

For model comparison, report exact generation settings, one fixed decoding policy,
per-family metrics, and both macro family average and overall micro average. Do not
tune on the test split.

## Limitations

- These are generated elementary problems, not novel research proofs.
- Correct final values and witnesses do not prove that the preceding prose is a
  faithful derivation. The reasoning-presence signal is intentionally weak.
- Natural-language parsing necessarily imposes a small formatting convention.
- Test-only templates are only a lightweight family-generalization check because
  their underlying mathematics may appear in a pretrained model.
- The verifier checks mathematical correctness, not whether a model memorized a
  generated instance. Freeze and withhold the test prompts during post-training.
- This suite complements rather than replaces theorem-proof benchmarks and any
  later isolated downstream certification experiment.

