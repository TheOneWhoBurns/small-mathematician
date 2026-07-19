#!/usr/bin/env python3
"""Select rows from one JSONL file in the ID order of another."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def rows(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ids-from", type=Path, required=True)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    identifiers = [row["id"] for row in rows(args.ids_from)]
    source = {row["id"]: row for row in rows(args.source)}
    if any(identifier not in source for identifier in identifiers):
        raise ValueError("missing ID")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("".join(json.dumps(source[identifier], sort_keys=True) + "\n" for identifier in identifiers))
    print(json.dumps({"rows": len(identifiers), "output": str(args.output)}, indent=2))


if __name__ == "__main__":
    main()
