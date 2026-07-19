#!/usr/bin/env python3
"""Merge labeled natural-language route prompt sets with strict ID checks."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, nargs="+", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    args = parser.parse_args()

    rows = []
    for path in args.input:
        rows.extend(json.loads(line) for line in path.read_text().splitlines() if line.strip())
    for row in rows:
        if not isinstance(row.get("id"), str) or not isinstance(row.get("prompt"), str):
            raise ValueError("every row needs string id and prompt")
        family = row.get("family", row.get("route"))
        if not isinstance(family, str):
            raise ValueError("every row needs family or route")
        row["family"] = family
    ids = [row["id"] for row in rows]
    if len(ids) != len(set(ids)):
        raise ValueError("duplicate IDs")
    rows.sort(key=lambda row: hashlib.sha256(f"route-merge-v1|{row['id']}".encode()).hexdigest())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
    manifest = {
        "schema_version": 1,
        "purpose": "frozen-readout training on original route prompts plus matched contrast-v1 development prompts",
        "sources": [{"path": str(path), "sha256": digest(path)} for path in args.input],
        "count": len(rows),
        "duplicate_ids": 0,
        "output": str(args.output),
        "output_sha256": digest(args.output),
    }
    args.manifest.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
