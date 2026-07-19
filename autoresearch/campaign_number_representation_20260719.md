# Number-representation campaign

## Question

Is the verified arithmetic cliff primarily caused by digit/positional representation, autoregressive Euclidean-chain length, or their interaction? Can a compact natural-language representation intervention improve verified cores without increasing model size or weakening the fixed verifier?

## Budget and stop

- Start: 2026-07-19 11:07 America/Guayaquil.
- Hard stop: 2026-07-19 18:00 America/Guayaquil, or immediately on user request. This supersedes the original 16:00 boundary at the user's request.
- Reserve the final 30 minutes for sealed evaluation, Lean compilation, ledger validation, and handoff.
- Actual stop: the user requested an early stop at approximately 15:49 America/Guayaquil. No further model generations were launched; only the in-flight compressed-prefix pass, scoring, Lean certification of the already-promoted staged outputs, and closeout checks were completed.

## Editable surface

- Natural-language rendering of numbers and Euclidean steps.
- Training curriculum and sampling mixture.
- Tokenizer/embedding handling only if a cheaper textual intervention fails and the comparison remains reproducible.

The arithmetic verifier, accepted-core definition, and Lean certificate builder remain fixed.

## Evaluation ladder

1. Measure a frozen 8-bit checkpoint on a balanced magnitude-by-chain-length diagnostic.
2. Compare decimal digits, number words, and explicit place-value text without training.
3. Train only the most justified representation on development data.
4. Promote only on a newly sealed parameter-disjoint paired test.
5. Compile every promoted core in Lean.

## Metrics and promotion

- Primary: strict `trace_valid` rate, paired against the unchanged decimal representation.
- Secondary: complete argument rate, performance in every magnitude/length cell, peak memory, throughput, and generated-token cost.
- A keeper must improve the preregistered target without significant regression in the established short/small cell. Loss, parsing, and formatting cannot override verified arithmetic.
- Diagnostic-set choices do not count as confirmation; a fresh sealed comparison is required.
