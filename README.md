# Small Mathematician

## Current result

The 596M-parameter model now produces strictly verified natural-language Euclidean arguments. Iteration 65 provides the strongest general promotion result: complete arguments improve from 37/200 to 60/200 (`p = 1.52e-5`) and verified computational cores from 69/200 to 88/200. The recommended iteration-67 specialist separately improves four-or-more-step cores from 17/100 to 26/100 (`p = 0.0117`) without significant short-chain harm. Its 8-bit deployment artifact is 633 MB, peaks at 0.807 GB during long-form inference, and runs about 49% faster than full precision on a fresh paired confirmation; verified cores move from 59/200 to 54/200, while complete arguments incur a measurable six-case loss.

Read [`CHECKPOINT_CARD.md`](CHECKPOINT_CARD.md) for the artifact contract and [`RESEARCH_REPORT.md`](RESEARCH_REPORT.md) for the evidence, failures, and next experiments.

Research question:

> How much mathematical problem-solving ability can be compressed into a natural-language-only model when formalization, theorem retrieval, and verification are delegated to a fixed external system?

## Architecture boundary

The small mathematician receives natural-language mathematical statements and emits natural-language proof blueprints. It never receives Lean source, proof states, tactic traces, or Mathlib lemma names.

Lean and Mathlib are isolated under `verifier/`. They are downstream infrastructure for a separate formalizer and are not small-model training data.

## Bootstrap contents

- `Qwen/Qwen3-0.6B-Base`: 0.6B-parameter Apache-2.0 base model for full post-training experiments.
- NaturalProofs 2.0.0: natural-language definitions, theorem/proof pairs, and reference links.
- FineProofs-SFT default split: natural-language olympiad problems, reasoning traces, proofs, broad categories, and quality metadata. These are candidate examples, not trusted truth.
- ProofBench: frozen natural-language proof evaluation. Its dataset card does not declare a license, so keep it evaluation-only pending clarification.
- MA-ProofBench: frozen natural-language analysis evaluation plus a separately stored Lean 4.28 view for downstream verification.
- Lean 4.28.0 and Mathlib v4.28.0: pinned verifier environment.
- MLX-LM: Apple-Silicon-native model loading and post-training stack.

Exact revisions, licenses, expected sizes, and checksums are recorded in `assets/sources.lock.json`.

## Bootstrap

```sh
./scripts/bootstrap.sh
```

The command is resumable. Downloads are written atomically, and known upstream checksums are verified before files are promoted into place.

## On-demand artifacts

Large checkpoints are stored as hash-pinned assets on the private GitHub release
`small-mathematician-artifacts-v1`, not in Git history. A lightweight checkout can
be restored to a runnable state with one command:

```sh
./scripts/hydrate.sh --profile train-specialist
```

Available profiles are:

- `inference`: restore the standalone 8-bit deployment model;
- `train-specialist`: restore the pinned Qwen base and iteration-67 parent;
- `train-general`: restore the base and iteration-65 general checkpoint;
- `history`: restore cold historical checkpoints;
- `all`: restore every retained model artifact.

Every download is checked against its byte count and SHA-256 digest from
`artifacts/manifest.json` before it is moved into place. The full bootstrap remains
available when raw public corpora, processed candidate views, or the Lean toolchain
must also be reconstructed.

## Verification

```sh
uv run python scripts/verify_bootstrap.py
uv run python scripts/smoke_model.py
(cd verifier && ELAN_HOME="$PWD/../.tools/elan" "$PWD/../.tools/elan/bin/lake" build)
```

## Data boundary

Generated views live under `assets/data/processed/`:

- `candidates/`: possible training material, not yet promoted to a trusted training split.
- `knowledge/`: natural-language definitions and references.
- `eval/`: frozen natural-language evaluation views.
- `verifier-only/`: formal statements that must never enter small-model prompts or training batches.

The bootstrap deliberately does not invent fine-grained concept labels. NaturalProofs titles/references and dataset categories are seed metadata; producing a reliable concept ontology is a research task, not a download step.

## Candidate-pool audit

```sh
uv run python scripts/build_candidate_pool.py
```

This creates an audited, deduplicated candidate pool without choosing a domain,
curriculum, or train/validation split. It removes FineProofs reasoning traces,
keeps only natural-language proof targets, assigns deterministic family IDs, and
checks candidate statements against sealed evaluation statements for likely
contamination. The resulting `eligible-default.jsonl` is a conservative starting
view, not a claim that those examples are correct or that its thresholds are final.
