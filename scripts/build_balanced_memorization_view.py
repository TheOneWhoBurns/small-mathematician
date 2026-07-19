#!/usr/bin/env python3
"""Build a deterministic balanced seen-example view for memorization diagnostics."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import defaultdict
from pathlib import Path


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--per-family", type=int, default=2)
    args = parser.parse_args()

    rows = [
        json.loads(line)
        for line in args.source.read_text().splitlines()
        if line.strip()
    ]
    selected: list[dict] = []
    counts: dict[str, int] = defaultdict(int)
    for row in rows:
        family = row.get("metadata", {}).get("family")
        if not isinstance(family, str):
            raise ValueError("every row must have metadata.family")
        if counts[family] < args.per_family:
            selected.append(row)
            counts[family] += 1
    if not counts or any(count != args.per_family for count in counts.values()):
        raise ValueError(f"insufficient balanced rows: {dict(counts)}")

    args.output.mkdir(parents=True, exist_ok=True)
    for split in ("train", "valid"):
        path = args.output / f"{split}.jsonl"
        with path.open("w", encoding="utf-8") as handle:
            for row in selected:
                handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
    manifest = {
        "schema_version": 1,
        "purpose": "seen-example memorization diagnostic only",
        "source": str(args.source),
        "source_sha256": sha256(args.source),
        "per_family": args.per_family,
        "family_counts": dict(sorted(counts.items())),
        "rows": len(selected),
        "train_equals_valid": True,
    }
    (args.output / "manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
