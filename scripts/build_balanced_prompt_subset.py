#!/usr/bin/env python3
"""Build a deterministic family-balanced JSONL prompt subset."""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--per-family", type=int, required=True)
    args = parser.parse_args()

    selected: dict[str, list[dict]] = defaultdict(list)
    for line in args.input.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        row = json.loads(line)
        family = row.get("family", row.get("metadata", {}).get("family"))
        if not isinstance(family, str):
            raise ValueError("every row needs a family")
        if len(selected[family]) < args.per_family:
            selected[family].append(row)

    if not selected or any(len(rows) != args.per_family for rows in selected.values()):
        raise ValueError({family: len(rows) for family, rows in selected.items()})

    # Interleave families so partial runs remain balanced.
    families = sorted(selected)
    output = [selected[family][index] for index in range(args.per_family) for family in families]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        "".join(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n" for row in output),
        encoding="utf-8",
    )
    print(json.dumps({"count": len(output), "families": families, "per_family": args.per_family}))


if __name__ == "__main__":
    main()
