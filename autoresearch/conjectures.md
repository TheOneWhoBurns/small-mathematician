# Conjectures

## C1: Compact blueprints make broad olympiad training feasible

- Status: open empirical hypothesis.
- Evidence: full reference arguments have median lengths around 1,642-2,101 tokens in number theory, algebra, combinatorics, and geometry, while 100% parameter training at 1536 tokens is memory-safe but only 0.115-0.120 updates/s.
- Smallest failure: a blueprint that omits a necessary construction or exceptional case may be short but useless to the formalizer.
- Next test: prepare audited compact blueprints, measure their per-domain token distributions, then compare broad family-balanced and narrow-domain curricula at equal training tokens.

## C2: Context should be selected by validation gain per wall-hour, not memory

- Status: supported as a design rule, not yet as a learning result.
- Evidence: peak Metal memory rose only from 3.414 GB at 512 tokens to 3.907 GB at 1536, while update time rose from roughly 2.6-3.0 seconds to 8.3-8.7 seconds.
- Smallest failure: if shorter caps truncate key ideas, their faster updates may be false economy.
- Next test: compare 512/1024/1536 on the same family split and equal non-padding token budget after compact-blueprint preparation.

## C3: The small mathematician contributes information the formalizer cannot recover alone

- Status: untested central conjecture.
- Evidence: none yet; proxy loss cannot establish it.
- Falsifier: model, corrupted, generic, and no-blueprint conditions have indistinguishable faithful Lean-verified solve rates under a frozen formalizer.
- Next test: bind a reproducible external formalizer and run the six paired conditions in `configs/experiment.v1.json`.

## Active

No active conjectures yet.

## Refuted

No refuted conjectures yet.

## Promoted

No promoted conjectures yet.
