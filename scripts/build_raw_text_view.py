#!/usr/bin/env python3
"""Convert prompt/completion JSONL into a raw causal-text training view."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--separator", default="\nSolution:\n")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    hashes = {}
    counts = {}
    for split in ("train", "valid", "test"):
        source = args.input / f"{split}.jsonl"
        target = args.output / f"{split}.jsonl"
        hasher = hashlib.sha256()
        count = 0
        with source.open(encoding="utf-8") as reader, target.open("w", encoding="utf-8") as writer:
            for line in reader:
                row = json.loads(line)
                output = {
                    "text": row["prompt"].rstrip() + args.separator + row["completion"].strip(),
                    "metadata": row.get("metadata", {}),
                }
                rendered = json.dumps(output, ensure_ascii=False, sort_keys=True) + "\n"
                writer.write(rendered)
                hasher.update(rendered.encode())
                count += 1
        hashes[split] = hasher.hexdigest()
        counts[split] = count
    manifest = {
        "schema_version": 1,
        "source": str(args.input),
        "format": "raw causal natural-language text",
        "separator": args.separator,
        "counts": counts,
        "sha256": hashes,
        "chat_template_used": False,
        "formal_data_read": False,
    }
    (args.output / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
