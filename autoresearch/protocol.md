# Autoresearch Protocol

The frozen machine-readable contract is `configs/experiment.v1.json`; the full rationale is `EXPERIMENT_DESIGN.md`.

## Objective

Maximize mathematical value added by a 596,049,920-parameter natural-language-only model while minimizing wall time, unified memory, model bytes, and downstream formalizer work. Formalization, retrieval, and Lean verification remain external and fixed within every scientific comparison.

## Editable surface

- Full-parameter post-training recipe, curriculum, and family-balanced sampling.
- Natural-language concept labels and compact proof-blueprint schema.
- Autoresearch proposal logic and proxy evaluator.

The sealed final benchmarks, verifier-only data, scorer definition, and a bound formalizer are not editable during a comparison.

## Evaluation commands

Local full-parameter training:

```sh
uv run python scripts/train_all_parameters.py --model assets/models/qwen3-0.6b-base --data RUN_DATA --output-dir RUN_OUTPUT --optimizer adafactor --batch-size 1 --iters N --max-seq-length CAP --grad-checkpoint --mask-prompt --seed SEED
```

Design validation:

```sh
uv run python scripts/score_formalizer_results.py --config configs/experiment.v1.json --check-config
```

Scientific scoring is blocked until `status` is `frozen_formalizer_bound`, then uses the benchmark command in the config.

## Metrics and budget

- Scientific primary metric: maximize paired percentage-point uplift in faithful Lean-verified solves, `model_blueprint - no_blueprint`, with a family-cluster confidence interval.
- Tonight's proxy frontier: maximize deterministic held-out answer and certificate correctness while minimizing family-held-out completion loss and wall time and maximizing structured-output rate, subject to retention, peak memory, and checkpoint size. Completion loss or format validity may never compensate for a measured correctness regression.
- Hard stop: 2026-07-19 09:00 America/Guayaquil. Reassess at least every 45 minutes; reserve the final 45 minutes for validation, checkpoint pruning, and ledger audit.
- Compare training recipes at equal non-padding token budgets and generation systems at equal downstream budgets.

## Promotion rule

A proxy winner is retained only if it does not regress deterministic held-out correctness and remains on the validation Pareto frontier; a surprising winner receives another seed. It is a candidate, not a mathematical result. Scientific promotion additionally requires positive paired uplift whose 95% family-cluster interval excludes zero, superiority to corrupted and generic blueprint controls, and no statement-faithfulness regression.

## Validation and attacks

- Split the audited eligible pool by `family_id`; no family or content may cross train, validation, or frozen internal test.
- Attack candidates with paraphrases, changed assumptions, irrelevant concept cues, corrupted length/domain-matched blueprints, generic blueprints, and plausible false steps.
- ProofBench and MA-ProofBench remain sealed and cannot guide autoresearch.
- A Lean proof counts only when its formalized statement separately passes the frozen faithfulness check.

## Ledger and checkpoints

Append every attempt, exact command, config hash, result, decision, failure mode, and next question to `ledger.jsonl`. Preserve failures. Keep only the baseline, current and previous reproducible proxy leaders, and scientific-evaluation candidates; preserve logs/configs before deleting dominated checkpoints.
