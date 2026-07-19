#!/usr/bin/env python3
"""Encode or decode fixed-width decimal numerals in selected JSONL text fields."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


INTEGER = re.compile(r"-?\d+")


def encode_number(text: str, width: int) -> str:
    value = int(text)
    if abs(value) >= 10**width:
        raise ValueError(f"{value} does not fit width {width}")
    sign = "-" if value < 0 else ""
    return sign + str(abs(value)).zfill(width)


def transform(text: str, operation: str, width: int) -> str:
    if operation == "encode":
        return INTEGER.sub(lambda match: encode_number(match.group(), width), text)
    return INTEGER.sub(lambda match: str(int(match.group())), text)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--operation", choices=("encode", "decode"), required=True)
    parser.add_argument("--width", type=int, default=4)
    parser.add_argument("--fields", nargs="+", default=["prompt", "completion", "response", "prediction"])
    args = parser.parse_args()
    if args.width < 1:
        parser.error("--width must be positive")

    rows = [json.loads(line) for line in args.input.read_text(encoding="utf-8").splitlines() if line.strip()]
    transformed = []
    touched = 0
    for row in rows:
        updated = dict(row)
        for field in args.fields:
            if isinstance(updated.get(field), str):
                value = transform(updated[field], args.operation, args.width)
                touched += int(value != updated[field])
                updated[field] = value
        transformed.append(updated)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("".join(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n" for row in transformed), encoding="utf-8")
    print(json.dumps({"rows": len(rows), "fields_touched": touched, "operation": args.operation, "width": args.width, "output": str(args.output)}, indent=2))


if __name__ == "__main__":
    main()
