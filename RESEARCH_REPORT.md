# Small Mathematician research report

## Research question

> How much mathematical problem-solving ability can be compressed into a very small, memory- and time-efficient, natural-language-only model when formalization, theorem retrieval, and Lean verification are delegated to a fixed external system?

## Answer so far

A 596-million-parameter model can learn a real but sharply bounded mathematical procedure on this computer. It can produce complete, multi-step natural-language Euclidean arguments that survive an arithmetic chain checker and Lean compilation on unseen numeric instances and unseen problem phrasings. The recommended iteration-67 specialist fits in a 1.19 GB file, uses about 1.36 GB peak memory for long-form inference, and was fully post-trained at a 5.56 GB peak.

The capability is not broad. The predecessor succeeds on 32% of a 200-case small-number test and 3.5% of a matched-size large-number test. On a fresh promotion test, iteration 65 improves its parent from 27% to 46% complete small arguments and from 10% to 14% medium arguments. A fixed downstream system raises the promoted checkpoint’s fresh-test coverage to 67% small and 21% medium by using correct model-generated Euclidean cores even when the model’s last sentence is wrong.

Iteration 67 adds a targeted result: on a fresh trace-length-controlled test, correct four-or-more-step computational cores improve from 17% to 26% (`p = 0.0117`) without significant short-chain harm. Its complete-argument and overall gains are not significant, so it is a long-computation specialist rather than evidence of broad proof improvement.

An independently tested 8-bit deployment version cuts the weight file from 1.192 GB to 633 MB and inference peak from 1.355 GB to 0.807 GB while increasing throughput from 0.586 to 0.872 problems/second on the fresh confirmation run. Its verified-core count is 54 versus 59 for full precision (`p = 0.180`), but complete arguments fall from 41 to 35 (`p = 0.0313`). The quantized artifact is therefore recommended for the checked-core architecture, not as a lossless replacement for model-complete proofs.

This supports the proposed division of labor:

1. The small model reads a natural-language statement and emits the mathematical idea plus numerical argument.
2. A tiny frozen head can route the statement to a concept label.
3. A fixed checker rejects false arithmetic.
4. A fixed formalizer retrieves the relevant theorem and compiles the accepted claims in Lean.

Lean vocabulary and Mathlib lemma names do not need to occupy the small model’s weights.

## What changed the result

### Full informal proofs did not work

Training full prose drove held-out likelihood loss down dramatically but produced no certifiable arguments. The model learned proof-shaped language, fabricated arithmetic, and looped. This falsified the assumption that lower prose loss was a useful proxy for mathematical execution.

### Atomic claims created the first signal

Restricting the model to a single gcd-and-divisibility sentence produced the first statistically nontrivial improvement. On the 200-case parameter-disjoint atomic test, curriculum scaling improved exact verified claims from 19 to 32 (`9.5%` to `16.0%`, paired exact `p = 0.035`). Component analysis showed that much of this gain was extraction and relation classification; exact gcd accuracy rose only from `20.5%` to `24.5%`.

Language diversity alone was not enough. On four newly held-out phrasings, performance moved from 10 to 16 of 200, but the paired result was not significant (`p = 0.307`). Exact gcd computation remained the bottleneck.

### Checkable Euclidean traces produced actual arguments

The model was then trained to emit every Euclidean division in natural language before its final claim. The verifier required:

- exact extraction of both operands and target;
- a valid quotient and remainder at every step;
- remainder bounds;
- a connected chain ending in remainder zero;
- the correct gcd and divisibility conclusion.

Oracle preflight passed all 1,160 train/validation/test rows, while all quotient-flipped and relation-flipped mutants failed. The untouched checkpoint scored 0/200 complete traces. After 300 updates, the trace checkpoint scored 7/200 on unseen large-number problems, with seven helped and zero harmed (`p = 0.015625`). Lean compiled 31 model-generated division equalities and seven conclusions.

On a separately sealed small-number test, the same checkpoint—without small-number fine-tuning—scored 64/200 complete arguments. It generated 103 fully correct Euclidean chains, but attached a wrong final sentence to 39 of them. Lean compiled all 198 equalities in the 64 complete outputs. The fixed external path compiled all 312 equalities in the 103 correct cores and derived the conclusions downstream.

An attempted small-only continuation was killed at update 200: validation loss worsened from `0.054` to `0.070` while training loss fell to `0.011`. No checkpoint was saved and the frozen parent prediction file remained the only test submission.

### A fresh medium curriculum improved the short procedure

A final curriculum was trained only on new coefficient-217–1,000 train/development instances. Before training, iteration-61 predictions were sealed on a fresh test containing 100 small and 100 medium cases. After 300 updates, validation loss was essentially flat (`0.057` to `0.056`), so promotion depended entirely on the paired capability test.

Complete arguments improved from 37/200 to 60/200: 26 helped, three harmed, paired exact `p = 1.52e-5`. Correct cores improved from 69 to 88 (`p = 5.46e-4`). The gain concentrated on fresh small problems, 27% to 46% complete (`p = 2.10e-5`); medium moved from 10% to 14% and was not significant. This checkpoint was promoted because it substantially improves the reliable short-trace regime without measurable forgetting, not because it solved the numeric-range extension.

### Trace length, not coefficient size, exposed the next bottleneck

Post-hoc stratification of the iteration-65 promotion test showed that its decisive gains occurred only on one-to-three-step Euclidean chains. Complete accuracy rose from `20.4%` to `38.1%` there (`p = 1.10e-5`), while four-to-five-step gains were not significant and six-plus-step performance did not improve.

A fresh curriculum therefore used only development examples requiring at least four divisions. The baseline and candidate were sealed before the private 100-short/100-long verifier was opened. Exact complete arguments moved from 28 to 35 overall (`p = 0.118`). Core-valid long computations moved from 17 to 26, with ten helped and one harmed (`p = 0.0117`); short cores moved from 20 to 19 (`p = 1.0`). Lean compiled 143 equalities in 35 complete arguments and 177 equalities in 45 core-valid arguments. This supports a narrow specialist promotion while leaving the stronger general significance claims with iteration 65.

### Eight bits is the practical quantization boundary

Naive affine quantization was tested at 8, 6, and 4 bits under identical greedy decoding. Eight-bit reduced peak inference memory by about 40% and improved throughput by about 49% on the independently sealed confirmation. Six-bit significantly reduced complete arguments from 35 to 6 and cores from 45 to 21 on the diagnostic suite. Four-bit reverted to generic base-model prose and produced zero parseable exact-format outputs.

The fresh 200-case eight-bit confirmation excluded 7,078 previously used parameter triples and passed all oracle checks before either prediction set was opened. Full precision scored 41 complete and 59 core-valid; eight-bit scored 35 complete and 54 core-valid. Lean compiled all 151 equalities in the 35 accepted complete outputs and all 227 equalities in the 54 accepted cores. This demonstrates a viable 633 MB deployment artifact while also showing that the learned procedure is sensitive to rounding below eight bits.

## Evidence table

| Experiment | Sealed evaluation | Result | Interpretation |
|---|---:|---:|---|
| Full prose completion | balanced near/paraphrase audits | 0 certifiable | Surface likelihood is not execution |
| Atomic Diophantine claim | 200 disjoint cases | 19→32, `p=0.035` | Real narrow gain, mostly extraction/relation |
| New-language atomic claim | 200 disjoint cases | 10→16, `p=0.307` | Directional, not conclusive |
| Full Euclidean trace, large | 200 disjoint cases | 0→7 complete, `p=0.0156` | First multi-step learned argument |
| Same trace model, small | 200 disjoint cases | 64 complete; 103 core-valid | Strong bounded arithmetic regime |
| Frozen numeric scale map | 80 cases per band | complete: 10%, 8.75%, 1.25% | Arithmetic cliff begins above 500 |
| Fresh medium curriculum | 200 paired cases | complete 37→60, `p=1.52e-5` | Promoted; gain concentrated on small |
| Trace-length curriculum | 200 paired cases | long core 17→26, `p=0.0117` | Validated long-chain specialist |
| Fresh 8-bit confirmation | 200 paired cases | core 59→54, `p=0.180`; complete 41→35, `p=0.0313` | Deployable for checked cores, not lossless |
| Frozen five-way method router | 100 contrast cases | 96%; 92% pairs | Concept routing survives specialization |

## Efficiency

- Model weights: 1,192,134,923 bytes.
- All-parameter training: 596.05M trainable parameters.
- Peak full training memory: 5.555 GB Metal.
- Peak long-form inference memory: 1.360 GB Metal.
- Large trace generation: 200 problems in 390.6 seconds, 0.512 problems/second.
- Small trace generation: 200 problems in 283.5 seconds, 0.706 problems/second.
- Frozen method router: 5,120 parameters, 30,984 bytes, about 11.2 prompts/second including model load on iteration 67.
- Eight-bit weights: 633,443,038 bytes; 0.807 GB inference peak; 0.872 fresh problems/second.
- Six-bit weights: 484,446,856 bytes; rejected for capability loss.
- Four-bit weights: 335,450,548 bytes; rejected for complete behavioral collapse.

## Correct architectural boundary

The strict result is the model-complete rate: 32% small and 3.5% large. The more useful deployed architecture may instead ask the model only for a checkable computational core. Under that contract, coverage is 51.5% small and 6.0% large; the fixed layer verifies the core and supplies theorem application. This does not prove the model knows the theorem conclusion, so both metrics must remain visible.

The external layer is not merely rubber-stamping model prose. It rejects fabricated arithmetic, checks chain structure, retrieves one fixed theorem, and asks Lean to certify the numerical facts and final proposition. The small model remains natural-language-only.

### Numeric reliability map

The frozen checkpoint was evaluated without further fitting on three more parameter-disjoint bands. Complete/core-valid rates were `10%/20%` for coefficients 217–500, `8.75%/12.5%` for 501–1,000, and `1.25%/1.25%` for 1,001–2,500. Parsing remained between 96.25% and 97.5%. This locates a sharp arithmetic-execution cliff rather than a prompt-format failure.

## Next experiment ladder

1. Retain intermediate validation checkpoints so a step-150 minimum can be compared honestly with the final step rather than inferred from loss alone.
2. Separate the output contract into “compute a verified Euclidean core” and “state the conclusion”; measure whether removing the unreliable last sentence improves usable precision.
3. Test verifier-guided multi-sample decoding on development data, then seal a fresh test before selecting sampling temperature or candidate count.
4. Add a second concept with a genuinely different procedure, such as polynomial value-difference obstruction, while replaying the Diophantine tests for forgetting.
5. Test whether a compact adapter on the rejected 4-bit backbone can recover verified execution without exceeding the 8-bit deployment footprint.

## Reproducibility

The append-only ledger contains 73 numbered iterations with hypotheses, commands or change descriptions, hashes, decisions, failures, and next questions. Benchmark manifests pin test prompt and verifier hashes. Prediction files were generated and hashed before private verifiers were opened. Lean files and manifests preserve the accepted subsets and certificate hashes.

See `CHECKPOINT_CARD.md` for the promoted artifact and `autoresearch/ledger.jsonl` for the complete audit trail.
