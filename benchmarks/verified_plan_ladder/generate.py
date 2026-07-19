#!/usr/bin/env python3
"""Generate deterministic public prompts, matched targets, and private verifier rows."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

from benchmark import DATA, DEFAULT_SEED, SPLIT_COUNTS, generate_instances, one_fact_mutant, write_jsonl


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=DEFAULT_SEED)
    parser.add_argument("--output", type=Path, default=DATA)
    args = parser.parse_args()
    instances = generate_instances(args.seed)
    args.output.mkdir(parents=True, exist_ok=True)
    manifest: dict[str, object] = {"schema_version": 1, "seed": args.seed, "split_counts_per_family": SPLIT_COUNTS, "splits": {}}
    for split in SPLIT_COUNTS:
        rows = [row for row in instances if row.split == split]
        paths = {
            "prompts": args.output / f"{split}.prompts.jsonl",
            "targets": args.output / f"{split}.targets.jsonl",
            "verifier": args.output / f"{split}.verifier.jsonl",
            "mutants": args.output / f"{split}.mutants.jsonl",
        }
        write_jsonl(paths["prompts"], (row.public() for row in rows))
        write_jsonl(paths["targets"], (row.targets() for row in rows))
        write_jsonl(paths["verifier"], (row.private() for row in rows))
        write_jsonl(paths["mutants"], ({"id": row.id, "family": row.family, "condition": "ordered", "response": one_fact_mutant(row)} for row in rows))
        manifest["splits"][split] = {
            "count": len(rows),
            "families": dict(sorted(Counter(row.family for row in rows).items())),
            **{f"{name}_sha256": sha256(path) for name, path in paths.items()},
        }
    (args.output / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

