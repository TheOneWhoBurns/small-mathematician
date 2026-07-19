# Small Mathematician checkpoint card

## Recommended checkpoint

- Base: Qwen3-0.6B-Base
- Parameters: 596.05 million, all updated during post-training
- Weights: `runs/iter067-trace-length-v7/weights.safetensors`
- SHA-256: `1c9fb3ed91625721ae610c6d13e981de25b4070faf04c8b3f0ec152673b30a2b`
- Stored size: 1,192,134,923 bytes
- Full-parameter training peak: 5.555 GB Metal memory
- Long-form inference peak: 1.360 GB Metal memory
- Long-form inference throughput: 0.512 problems/second on the 200-case large trace test

The model receives only natural-language statements and concept labels. It was never trained on Lean source, tactic states, theorem names, or Mathlib lemma names. It emits a natural-language Euclidean-algorithm argument. Parsing, verification, theorem retrieval, and Lean compilation are fixed external components.

## Recommended accuracy procedure

Use the iteration-89 first-step specialist for at most the first 60 generated tokens, extract its first valid natural-language Euclidean sentence, then unload it and continue with iteration 67 for at most 230 tokens.

- First-step weights: `runs/iter089-first-step-loss-full/weights.safetensors`
- First-step SHA-256: `60b8a636906908e4f3dc0d984f0ba7a8e291f30bab5582f28d41a74ac5671f2c`
- Continuation weights: the iteration-67 checkpoint above
- Fresh v18 strict cores: 82/300 single-model versus 92/300 staged
- Paired result: 13 helped, three harmed, exact `p = 0.0213`
- Runtime: one checkpoint resident at a time; 1.393 GB measured peak
- Storage: two 1,192,134,923-byte full checkpoints
- Hydration profile: `./scripts/hydrate.sh --profile accuracy`

The staged procedure is the accuracy recommendation because its strict-core gain replicated on a fresh parameter-disjoint suite. It is not a broader-model claim: semantic complete arguments moved from 60 to 67 (`p = 0.0654`), and the final sentence barely changed. Lean compiled all 362 generated Euclidean equalities in the 92 checker-accepted staged cores.

## Deployment checkpoint

- Model directory: `runs/iter069-iter067-8bit/`
- Weight file: 633,443,038 bytes
- Weight SHA-256: `1f8ea0aae28fbefeb73a9cec6a7a4a597d580102d9f9faba1a18cdfa2ac27d1f`
- Quantization: 8-bit affine, group size 64, 8.501 effective bits per weight
- Peak long-form inference memory: 0.807 GB
- Fresh-test throughput: 0.872 problems/second

This is the recommended artifact when memory and speed matter. Against full precision on a fresh paired 200-case confirmation, verified cores moved from 59 to 54 (`p = 0.180`) while complete arguments moved from 41 to 35 (`p = 0.0313`). It therefore preserves the fixed-verifier core architecture well, but it is not lossless for complete model-only arguments. The full-precision checkpoint above remains the accuracy reference.

## Verified capability

All reported test instances are parameter-disjoint from training and use problem-statement templates absent from training.

Iteration 65 remains the strongest general promotion result. Its fresh paired 200-case suite contains 100 small problems and 100 medium problems, compared with the frozen iteration-61 parent.

| Fresh promotion split | Iteration 61 complete/core | Iteration 65 complete/core |
|---|---:|---:|
| Small | 27% / 52% | 46% / 67% |
| Medium, coefficients 217–1,000 | 10% / 17% | 14% / 21% |
| Overall | 18.5% / 34.5% | 30% / 44% |

Complete arguments improved from 37 to 60: 26 helped, three harmed, paired exact `p = 1.52e-5`. Correct cores improved from 69 to 88: 24 helped, five harmed, `p = 5.46e-4`. The small split improvement is decisive; the four-point medium improvement is directional and not significant.

Iteration 67 is the recommended long-chain specialist. It was trained only on fresh examples requiring at least four Euclidean divisions and compared with iteration 65 on another sealed 200-case suite.

| Fresh trace-length split | Iteration 65 complete/core | Iteration 67 complete/core |
|---|---:|---:|
| At most three steps | 12% / 20% | 14% / 19% |
| At least four steps | 16% / 17% | 21% / 26% |
| Overall | 14% / 18.5% | 17.5% / 22.5% |

The preregistered long-chain core target improved from 17 to 26: ten helped, one harmed, paired exact `p = 0.0117`. Short-chain core performance was statistically unchanged. Overall complete and core gains were not significant, so iteration 67 is a validated specialist, not a new general-proof claim.

The predecessor’s separately sealed scale map remains useful for locating the arithmetic cliff:

| Test | Complete model argument | Correct Euclidean core | Untouched pre-trace baseline |
|---|---:|---:|---:|
| Small operands, maximum coefficient 216 | 64/200 (32.0%) | 103/200 (51.5%) | not used for promotion |
| Coefficients 217–500 | 8/80 (10.0%) | 16/80 (20.0%) | not measured |
| Coefficients 501–1,000 | 7/80 (8.75%) | 10/80 (12.5%) | not measured |
| Coefficients 1,001–2,500 | 1/80 (1.25%) | 1/80 (1.25%) | not measured |
| Larger operands, maximum coefficient about 9,450 | 7/200 (3.5%) | 12/200 (6.0%) | 0/200 complete |

“Complete model argument” requires every generated division equality, the Euclidean chain, the gcd, target extraction, and the model’s final divisibility sentence to be correct. “Correct Euclidean core” ignores the model’s last sentence; the fixed system verifies the model-computed trace and derives the conclusion itself.

The predecessor’s large-test gain over the untouched pre-trace checkpoint is paired-exact significant: seven helped, zero harmed, `p = 0.015625`. The small-versus-large complete-argument difference has Fisher exact `p = 9.53e-15` and odds ratio `12.97`.

The intermediate bands show that the main reliability cliff occurs above coefficient 500. Output parsing remains above 95% in every band; arithmetic validity is what collapses.

Lean compiled:

- 35 complete iteration-67 arguments containing 143 model-generated Euclidean equalities and 35 derived conclusions.
- The fixed-external-system path for 45 iteration-67 cores containing 177 generated equalities.
- 60 complete promotion-test arguments containing 193 model-generated Euclidean equalities and 60 derived conclusions.
- The fixed-external-system path for 88 promotion-test cores containing 278 generated equalities.
- 64 complete small-number arguments containing 198 model-generated Euclidean equalities and 64 derived conclusions.
- Seven complete large-number arguments containing 31 generated equalities and seven derived conclusions.
- The fixed-external-system path for 103 small and 12 large correct Euclidean cores.

The unchanged 31 KB frozen method router scores 96/100 statements and 92% matched-pair accuracy on iteration 67, with all 20 Diophantine statements routed correctly.

The standalone 8-bit deployment model preserves exactly the same 96/100 routing score and 92% matched-pair score.

The most recent diagnostic revises the causal story. In a balanced magnitude-by-chain-length suite, chain length alone was near random for predicting failure (`AUC = 0.503`), while magnitude plus digit features reached `0.779` and the combined feature set reached `0.800`. On 480 traces, 227 first failed at step one and 92 at step two; only 30 first failed at step three or later. Decimal digits are linearly decodable from hidden states, but magnitude probes fail out of range. The current bottleneck is best described as brittle use of number magnitude and the first quotient-remainder transition, with later chain accumulation secondary.

## Example accepted output

Problem: Could a balance change by exactly -48 using arbitrary signed groups of 55 and 45?

> Euclidean step: 55 = 1 times 45 plus 10. Euclidean step: 45 = 4 times 10 plus 5. Euclidean step: 10 = 2 times 5 plus 0. Therefore the greatest common divisor is 5, and it does not divide -48.

Every equality and the final conclusion compile in Lean through the fixed certificate layer.

## Limitations

- This is one narrow concept: linear Diophantine solvability via the Euclidean algorithm.
- Reliability collapses with numeric scale.
- The iteration-65 medium-band gain is not individually significant; most of its fresh-test improvement is on short traces.
- Iteration 67 significantly improves only the targeted long-chain core metric; its overall and complete-argument gains are not significant.
- Fluent invalid arithmetic remains common; low validation loss is not a safety signal.
- The 96% router is a synthetic five-way closed-set test, not broad mathematical understanding.
- The 51.5% small “core” rate is not the model-complete rate: a fixed downstream layer supplies the theorem application and corrects the final conclusion.
- Naive 6-bit and 4-bit affine quantization fail badly: 6-bit falls to 6/200 complete and 21/200 core-valid on the diagnostic suite; 4-bit produces no parseable exact-format output. The learned full-post-training deltas are unusually quantization-sensitive below eight bits.
- The staged accuracy procedure doubles checkpoint storage even though only one checkpoint is resident at a time.
- The 596,125,674-byte int8 specialist delta preserved first-step behavior on v18, but is not promoted: no end-to-end staged verification was run after the early stop, and reconstruction peaked at 1.956 GB.

## Reproduction anchors

- Full append-only ledger: `autoresearch/ledger.jsonl`
- Large trace benchmark: `benchmarks/diophantine_trace_v4/`
- Small trace benchmark: `benchmarks/diophantine_trace_small_v5/`
- Large strict report: `runs/iter061-trace-v4/candidate.report.json`
- Small strict report: `runs/iter062-trace-small-v5/baseline-iter061.report.json`
- Large complete Lean file: `verifier/GeneratedIter061TraceClaims.lean`
- Small complete Lean file: `verifier/GeneratedIter062SmallTraceClaims.lean`
- Small core-pipeline Lean file: `verifier/GeneratedIter062SmallTraceCorePipeline.lean`
- Promotion paired report: `runs/iter065-trace-curriculum-v6/paired-comparison.json`
- Promotion complete Lean file: `verifier/GeneratedIter065CurriculumComplete.lean`
- Promotion core Lean file: `verifier/GeneratedIter065CurriculumCore.lean`
- Trace-length paired report: `runs/iter067-trace-length-v7/paired-comparison.json`
- Trace-length core paired report: `runs/iter067-trace-length-v7/paired-core-comparison.json`
- Trace-length complete Lean file: `verifier/GeneratedIter067TraceLengthComplete.lean`
- Trace-length core Lean file: `verifier/GeneratedIter067TraceLengthCore.lean`
- 8-bit quantization manifest: `runs/iter069-iter067-8bit/quantization_manifest.json`
- Fresh 8-bit paired complete report: `runs/iter072-quant-confirmation-v8/paired-complete.json`
- Fresh 8-bit paired core report: `runs/iter072-quant-confirmation-v8/paired-core.json`
- Fresh 8-bit complete Lean file: `verifier/GeneratedIter072EightBitComplete.lean`
- Fresh 8-bit core Lean file: `verifier/GeneratedIter072EightBitCore.lean`
- First-step specialist: `runs/iter089-first-step-loss-full/weights.safetensors`
- Fresh staged paired core report: `runs/iter095-staged-prefix-confirmation-v18/paired-trace_valid.json`
- Fresh staged core Lean file: `verifier/GeneratedIter095StagedCore.lean`
- Experimental int8 specialist delta report: `runs/iter096-specialist-int8-delta/v18-prefix-comparison.report.json`
