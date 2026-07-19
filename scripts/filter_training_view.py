#!/usr/bin/env python3
"""Filter a JSONL training view by public metadata without changing examples."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-dir", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--family", required=True)
    args = parser.parse_args()

    args.output_dir.mkdir(parents=True, exist_ok=True)
    counts: dict[str, int] = {}
    hashes: dict[str, str] = {}
    for split in ("train", "valid"):
        source = args.source_dir / f"{split}.jsonl"
        rows = [
            json.loads(line)
            for line in source.read_text().splitlines()
            if line.strip()
        ]
        selected = [
            row
            for row in rows
            if row.get("metadata", {}).get("family") == args.family
        ]
        if not selected:
            raise ValueError(f"no {args.family} rows in {source}")
        output = args.output_dir / f"{split}.jsonl"
        with output.open("w", encoding="utf-8") as handle:
            for row in selected:
                handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
        counts[split] = len(selected)
        hashes[split] = sha256(source)

    manifest = {
        "schema_version": 1,
        "source_dir": str(args.source_dir),
        "source_sha256": hashes,
        "filter": {"metadata.family": args.family},
        "counts": counts,
        "examples_modified": False,
    }
    (args.output_dir / "manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
