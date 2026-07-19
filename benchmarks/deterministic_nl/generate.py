#!/usr/bin/env python3
"""Generate the frozen public prompts and private verifier records."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

from benchmark import DATA, DEFAULT_SEED, generate_instances, validate_model_boundary, write_jsonl


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=DEFAULT_SEED)
    parser.add_argument("--dev-per-family", type=int, default=12)
    parser.add_argument("--test-per-family", type=int, default=20)
    parser.add_argument("--output", type=Path, default=DATA)
    args = parser.parse_args()

    instances = generate_instances(args.seed, args.dev_per_family, args.test_per_family)
    validate_model_boundary(instances)
    args.output.mkdir(parents=True, exist_ok=True)
    manifest: dict[str, object] = {
        "schema_version": 1,
        "seed": args.seed,
        "dev_per_family": args.dev_per_family,
        "test_per_family": args.test_per_family,
        "splits": {},
    }
    for split in ("dev", "test"):
        rows = [instance for instance in instances if instance.split == split]
        public_path = args.output / f"{split}.prompts.jsonl"
        private_path = args.output / f"{split}.verifier.jsonl"
        write_jsonl(public_path, (instance.public() for instance in rows))
        write_jsonl(private_path, (instance.private() for instance in rows))
        manifest["splits"][split] = {
            "count": len(rows),
            "families": dict(sorted(Counter(instance.family for instance in rows).items())),
            "public_sha256": file_sha256(public_path),
            "verifier_sha256": file_sha256(private_path),
        }
    manifest_path = args.output / "manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

