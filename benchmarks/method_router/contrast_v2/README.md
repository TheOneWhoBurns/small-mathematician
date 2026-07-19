# Method-router contrast v2

This is a newly authored held-out route-selection test for a router whose configuration was already fixed using contrast v1. It retains the controlled design of 50 matched pairs and 100 prompts, but uses five new story shells, new relation descriptions, new counterdecoy wording, a new seed, and a different response instruction.

Every unordered pair of the five routes occurs five times. Therefore each route appears exactly 20 times. Within each pair, both prompts have the same story shell, exact word count, and identical six numeric literals in identical order. Their operative mathematical dependencies differ and require different routes. Each prompt displays its counterpart's salient method noun on a decorative badge that explicitly contributes no constraint.

Run from this directory:

```sh
uv run --project ../../.. python generate.py
uv run --project ../../.. python self_test.py
```

The self-test validates counts, route balance, pair structure, exact word and number matching, counterpart decoys, forbidden gold phrases, route-specific mathematical well-formedness, and deterministic byte-for-byte regeneration. It also compares v2 directly against `../contrast/data/prompts.jsonl`: exact prompt overlap must be zero, and overlap between normalized eight-token n-grams must be zero. Numbers are normalized to `<num>` before the long-ngram comparison, so new parameter values cannot conceal reused prose.

The relation audit is authored and structural: it checks that each prompt contains the complete operative dependency for its assigned route and that its parameters are mathematically well formed. It does not use model agreement as ground truth.

This remains only a method-selection evaluation. It does not certify a proof, an executor, or a final answer with Lean. Its held-out interpretation is valid only if configuration and checkpoint selection were frozen before anyone inspected v2 model results.

