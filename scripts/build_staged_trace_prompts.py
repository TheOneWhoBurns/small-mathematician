#!/usr/bin/env python3
"""Build continuation prompts from a natural-language first-step source."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path


FIRST_STEP = re.compile(r"^Euclidean step: -?\d+ = -?\d+ times -?\d+ plus -?\d+\.")


def load(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--prompts", type=Path, required=True)
    parser.add_argument("--prefix-source", type=Path, required=True)
    parser.add_argument("--source-field", choices=("response", "completion", "expected"), required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    prompts = {row["id"]: row for row in load(args.prompts)}
    sources = {row["id"]: row for row in load(args.prefix_source)}
    if prompts.keys() != sources.keys():
        raise ValueError("prompt and prefix-source IDs do not match")

    rows = []
    parsed = 0
    for problem_id, row in prompts.items():
        source = " ".join(sources[problem_id][args.source_field].strip().split())
        match = FIRST_STEP.match(source)
        prefix = match.group(0) if match else ""
        parsed += int(bool(match))
        rows.append(
            {
                "id": problem_id,
                "family": row.get("family"),
                "surface": row.get("surface", "unspecified"),
                "prefix": prefix,
                "prefix_parsed": bool(match),
                "prompt": row["prompt"] + prefix + (" " if prefix else ""),
            }
        )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows), encoding="utf-8")
    manifest = {
        "count": len(rows),
        "prefix_parsed": parsed,
        "prompts_sha256": digest(args.prompts),
        "prefix_source_sha256": digest(args.prefix_source),
        "source_field": args.source_field,
        "output_sha256": digest(args.output),
    }
    args.output.with_suffix(args.output.suffix + ".manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(manifest, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
