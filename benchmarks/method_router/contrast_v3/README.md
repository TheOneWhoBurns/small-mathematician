# Method-router contrast v3

Contrast v3 is the third independently worded held-out route-selection set. It was created only after the iter039 and base probes were frozen and their selection seals recorded. Those exact probe and seal hashes are stored in `data/manifest.json` and verified by `self_test.py` against the local immutable artifacts.

The design remains fixed at 50 matched pairs and 100 prompts: all ten unordered route pairings occur five times and each route appears 20 times. Pair members share a newly authored story shell, exact word count, and the same six numeric literals in the same order. Their binding mathematical relations differ, and each displays its counterpart route's noun only as an obsolete non-operative cover mark.

Run from this directory:

```sh
uv run --project ../../.. python generate.py
uv run --project ../../.. python self_test.py
```

The self-test covers counts, matching, route balance, decoys, 100 authored semantic audits, parameter well-formedness, forbidden gold phrases, distinctive relation phrases from both prior sets, seal hashes, and deterministic byte-for-byte regeneration. It compares v3 against both v1 and v2 after replacing all numbers with `<num>`: exact prompt overlap and normalized eight-token n-gram overlap must both be zero for each prior version.

No model, lexical baseline, executor, or Lean prover is run here. This is a routing probe, not evidence of proof or answer correctness. Its held-out interpretation depends on the recorded probes and configurations having been sealed before v3 was opened.

