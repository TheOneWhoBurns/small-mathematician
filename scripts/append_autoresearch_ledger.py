#!/usr/bin/env python3
"""Validate and append pre-rendered JSONL records to the autoresearch ledger."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def rows(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ledger", type=Path, required=True)
    parser.add_argument("--records", type=Path, required=True)
    args = parser.parse_args()
    ledger_rows = rows(args.ledger)
    new_rows = rows(args.records)
    expected = ledger_rows[-1]["iteration"] + 1
    if [row["iteration"] for row in new_rows] != list(range(expected, expected + len(new_rows))):
        raise ValueError("new iterations are not contiguous after the current ledger")
    with args.ledger.open("a", encoding="utf-8") as handle:
        for row in new_rows:
            handle.write(json.dumps(row, separators=(",", ":"), ensure_ascii=False) + "\n")
    print(json.dumps({"appended": len(new_rows), "first": expected, "last": expected + len(new_rows) - 1}))


if __name__ == "__main__":
    main()
