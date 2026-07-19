#!/usr/bin/env python3
"""Collect unique (a, b, c) triples from verifier JSONL files."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    unique: dict[tuple[int, int, int], dict] = {}
    sources = 0
    for path in sorted(args.root.rglob("*.verifier.jsonl")):
        if path.resolve() == args.output.resolve():
            continue
        sources += 1
        for line in path.read_text(encoding="utf-8").splitlines():
            if not line.strip():
                continue
            row = json.loads(line)
            params = row.get("parameters")
            if isinstance(params, dict) and {"a", "b", "c"} <= params.keys():
                key = (params["a"], params["b"], params["c"])
                unique[key] = {"parameters": {"a": key[0], "b": key[1], "c": key[2]}}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in unique.values()), encoding="utf-8")
    print(json.dumps({"sources": sources, "unique_parameters": len(unique), "output": str(args.output)}, indent=2))


if __name__ == "__main__":
    main()
