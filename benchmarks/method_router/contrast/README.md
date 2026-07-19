# Matched method-router contrasts

This is a separate route-selection evaluation for the five-method natural-language router. It is designed to test whether a model follows the operative mathematical relations instead of copying a family noun.

There are 50 matched pairs, or 100 prompts. Every unordered pair of routes appears exactly five times, giving exactly 20 prompts per route. Within a pair, both prompts use the same neutral story shell, identical word count, and the same six numeric literals in the same order. The operative relation changes, so the correct routes differ. Each prompt also places the counterpart route's salient noun in an explicitly non-operative file title as a counterlexical decoy.

The `family` and `route` fields are intentionally identical route IDs for compatibility with the existing router evaluator. Only the natural-language `prompt` should be sent to a model. `pair_id`, labels, and metadata are evaluation transport.

Generate and validate from this directory:

```sh
uv run --project ../../.. python generate.py
uv run --project ../../.. python self_test.py
```

The validator checks deterministic byte-for-byte regeneration, 100 prompts, 50 two-sided pairs, 20 examples per route, five examples for every unordered route pair, different labels inside each pair, exact word-count and numeric-sequence matching, counterpart-route decoys, and absence of route IDs or distinctive gold-label phrases from prompt text.

This suite deliberately stops at route selection. The cross-route stories do not share a universal fixed executor, and no Lean certification or proof correctness is claimed. Treating them as certified mathematical solutions would be fake evidence; they are controlled tests of method recognition only.

