# Small Mathematician Experiment Design v1

## Research question

> How much mathematical problem-solving ability can be compressed into a very small, memory- and time-efficient, natural-language-only model when formalization, theorem retrieval, and Lean verification are delegated to a fixed external system?

The small model receives only a natural-language problem and emits only a natural-language list of relevant concepts plus a proof blueprint. It never sees Lean, proof states, tactic traces, or Mathlib lemma names. This is a capacity allocation decision: the 596M parameters should learn mathematical representations and reusable proof moves, while exact theorem retrieval and formal syntax live downstream.

## What is and is not measurable tonight

Two stages must not be conflated.

1. **Local development stage, available now.** Full-parameter post-training can be ranked by family-held-out completion loss, structured-output validity, audited concept-label metrics, truncation, wall time, peak memory, and checkpoint bytes. These are proxy metrics. They can select the next experiment but cannot establish mathematical ability.
2. **Frozen-formalizer stage, not yet available.** The scientific metric is the paired increase in faithful, Lean-verified solves caused by the small model's blueprint, relative to the identical formalizer receiving no blueprint. Before this stage runs, the external model/revision, prompt hash, decoding budget, retrieval snapshot, Lean/Mathlib versions, and statement-faithfulness checker must be bound in the config.

This interactive GPT-5.6 Sol agent is not itself a reproducibly frozen evaluator. It can prepare data and inspect failures. If GPT-5.6 is used as the formalizer, it must be exposed through a pinned endpoint or otherwise versioned invocation with the complete binding above.

## Measured local feasibility

Hardware: MacBook Air, Apple M4 (10 cores), 16 GB unified memory. Software: MLX 0.32.0 and MLX-LM 0.31.3. Model: pinned `Qwen/Qwen3-0.6B-Base` revision, 596,049,920 parameters.

The stock MLX-LM command called `full` freezes the embedding, final norm, and language-model head: it reported only 440.466M/596.050M trainable (73.898%). `scripts/train_all_parameters.py` calls `model.unfreeze()` and audibly guards the required 596.050M/596.050M (100%) contract.

Measured with batch size 1, Adafactor, completion-only loss, gradient checkpointing, seed 17, and three training updates on candidate-derived examples:

| Context cap | Peak Metal memory | Steady iteration rate | Approx. update time | Source log |
|---:|---:|---:|---:|---|
| 512 | 3.414 GB | 0.34-0.38 it/s | 2.6-3.0 s | `experiments/full_train_probe/probe-all-real512-seed17.log` |
| 1024 | 3.647 GB | 0.18-0.20 it/s | 5.1-5.7 s | `experiments/full_train_probe/probe-all-real1024-seed17.log` |
| 1536 | 3.907 GB | 0.115-0.120 it/s | 8.3-8.7 s | `experiments/full_train_probe/probe-all-real1536-seed17.log` |

These runs are timing probes, not learning experiments. Their three-step losses are meaningless. The generated probe weights were deleted after logs and configs were preserved.

The current audited eligible pool has 20,066 examples. Tokenization of `problem + concepts + full reference argument` shows:

| Pool/domain | Examples | Median tokens | 90th percentile | Fits 512 | Fits 1024 | Fits 1536 |
|---|---:|---:|---:|---:|---:|---:|
| Entire eligible pool | 20,066 | 425 | 1,833 | 56.6% | 77.5% | 86.5% |
| ProofWiki | 4,672 | 205 | 442 | 93.7% | 99.5% | 99.9% |
| Stacks | 11,519 | 428 | 1,118 | 58.8% | 87.5% | 95.7% |
| Number theory | 981 | 1,642 | 2,916 | 3.0% | 22.1% | 46.2% |
| Algebra | 574 | 1,665 | 3,049 | 3.1% | 20.7% | 43.4% |
| Combinatorics | 701 | 1,670 | 2,949 | 3.7% | 18.3% | 42.4% |
| Geometry | 918 | 2,101 | 3,326 | 0.8% | 9.0% | 25.2% |

Thus memory does not force a narrow domain. Long, teacher-written olympiad proofs force the tradeoff. The intended output is a compact proof blueprint, so the correct response is to measure post-preparation blueprint lengths rather than prematurely choosing ProofWiki or one olympiad domain.

## Leakage-resistant data contract

- Begin from `assets/data/processed/audited/eligible-default.jsonl` only.
- Split by `family_id`, never by individual example. Assign `sha256("small-mathematician-v1|" + family_id)` to 80% train, 10% validation, and 10% frozen internal test buckets.
- Assert that neither `family_id` nor `content_id` crosses splits. Before freezing, run a second cross-split near-duplicate audit because the current family key normalizes wording and numbers but is not a semantic equivalence oracle.
- Perform curriculum, schema, concept-label, and hyperparameter selection only on train and validation. Open internal test only after a recipe is frozen.
- ProofBench and MA-ProofBench remain sealed final evaluations. Their solutions, Lean views, and observed model failures cannot enter prompts, training examples, retrieval, curriculum decisions, or autoresearch proposals.
- The Lean MA-ProofBench view stays verifier-only. Statement overlap checks may use sealed statements, but never solutions, and their results can only exclude candidates.

Requested improvement to the pool interface: add a deterministic split builder that consumes `family_id`, emits a split manifest with source hashes and counts by domain, and fails on cross-split content/family overlap. Add a stronger stable `cluster_id` if the near-duplicate audit finds paraphrased families that `family_id` misses.

## Training comparison

All comparisons use equal non-padding training-token budgets, not equal updates, because sequence lengths differ. The main full-parameter command is:

```sh
uv run python scripts/train_all_parameters.py \
  --model assets/models/qwen3-0.6b-base \
  --data RUN_DATA_DIRECTORY \
  --output-dir RUN_OUTPUT_DIRECTORY \
  --optimizer adafactor \
  --batch-size 1 \
  --iters N \
  --learning-rate 1e-5 \
  --max-seq-length CONTEXT_CAP \
  --grad-checkpoint \
  --mask-prompt \
  --seed SEED
```

The first model baseline is the untouched Qwen3-0.6B Base generating the same blueprint schema under the same decoding budget. A retrieval-only blueprint is a non-parametric baseline. A trained checkpoint must beat both eventually; validation loss alone cannot establish that.

## Adaptive domain and context rule

Do not precommit to all domains, one domain, five-minute trials, or a single long run.

At each decision point:

1. Recompute token-length and family counts on the actual compact-blueprint dataset, by domain.
2. Eliminate a context cap only if it violates memory reserve, truncates more than the preregistered tolerance, or has worse validation gain per wall-hour than another cap.
3. Form the broadest family-balanced domain mixture that supplies enough distinct train and validation families within the remaining equal-token budget. Breadth has priority when cost is comparable; narrow only if a domain's long outputs or weak labels consume the budget without improving held-out proxies.
4. Stop a short trial as soon as it is confidently dominated, or when its declared token/wall budget expires. Re-run surprising winners with another seed.
5. Start one substantial run only when a proxy leader survives a second seed and enough time remains to finish, validate, save, and audit before 09:00.

The measured rates imply roughly 100 updates in five training minutes at 512, 55 at 1024, and 35 at 1536, before loading, evaluation, and checkpoint I/O. A 1,000-example pass is roughly 45 minutes at 512, 1.5 hours at 1024, or 2.4 hours at 1536 if each example is one update. These are scheduling estimates, not prescribed trial lengths.

Planning envelope before the hard stop: approximately 10-18 development cycles plus zero or one 2-4 hour substantial run, reserving the final 45 minutes for validation, checkpoint pruning, and ledger audit. Pause and realign at least every 45 minutes. The number of cycles is deliberately adaptive.

## Scientific evaluation with the frozen formalizer

Every theorem and generation seed is evaluated under the same downstream budget in six paired conditions:

- `no_blueprint`: original statement only;
- `base_model_blueprint`: blueprint from untouched Qwen3-0.6B Base;
- `model_blueprint`: blueprint from the candidate checkpoint;
- `corrupted_blueprint`: another theorem's length/domain-matched blueprint;
- `generic_blueprint`: plausible but non-problem-specific advice;
- `reference_argument`: audited human/teacher argument as an approximate ceiling.

A solve counts only when both the Lean proof verifies and the formalized Lean statement passes the separately frozen statement-faithfulness check. This prevents the system from proving an easier mistranslation.

Primary metric:

```text
mean(faithful_verified(model_blueprint) - faithful_verified(no_blueprint))
```

Report percentage-point uplift with a 95% family-cluster bootstrap interval, absolute solve rates, paired helped/harmed counts, trained-minus-base uplift, model-minus-corrupted/generic deltas, wall time, formalizer tokens, retrieval calls, and proof-attempt count. The formalizer must not receive condition labels.

Promotion requires positive paired uplift whose family-cluster interval excludes zero, superiority to corrupted and generic blueprints, and no statement-faithfulness regression. A powerful formalizer that ignores the blueprint should make all blueprint conditions converge toward `no_blueprint`; that is a valid negative result.

Once the formalizer binding is complete, score a result file with:

```sh
uv run python scripts/score_formalizer_results.py \
  --config configs/experiment.v1.json \
  --outcomes runs/frozen-formalizer/outcomes.jsonl
```

Until then, validate the frozen design without claiming scientific readiness:

```sh
uv run python scripts/score_formalizer_results.py \
  --config configs/experiment.v1.json \
  --check-config
```

## Checkpoint and ledger rules

- Keep only the untouched baseline, current proxy Pareto leader, previous reproducible leader, and any checkpoint queued for frozen-formalizer evaluation.
- A failed/dominated checkpoint may be deleted only after its exact command, config hash, metrics, failure mode, and next question are appended to `autoresearch/ledger.jsonl`.
- Keep at least 4 GiB immediately available for saving the next 1.1 GiB full checkpoint safely.
- No final-benchmark observation may appear in the autoresearch ledger before the recipe and formalizer are frozen.
- The mandatory stop is 2026-07-19 09:00 America/Guayaquil. Reserve the final 45 minutes for completion audit; do not start a run that cannot finish and save before then.
