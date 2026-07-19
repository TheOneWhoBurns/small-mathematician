#!/usr/bin/env python3
"""Build natural-language number-rendering views without changing targets."""

from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict
from pathlib import Path


INTEGER = re.compile(r"(?<![A-Za-z0-9])-?\d+(?![A-Za-z0-9])")
DIGIT_WORDS = ("zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine")
ONES = DIGIT_WORDS + ("ten", "eleven", "twelve", "thirteen", "fourteen", "fifteen", "sixteen", "seventeen", "eighteen", "nineteen")
TENS = ("", "", "twenty", "thirty", "forty", "fifty", "sixty", "seventy", "eighty", "ninety")
PLACES = ("ones", "tens", "hundreds", "thousands", "ten-thousands")


def words_positive(value: int) -> str:
    if value < 20:
        return ONES[value]
    if value < 100:
        return TENS[value // 10] + ("-" + ONES[value % 10] if value % 10 else "")
    if value < 1000:
        return ONES[value // 100] + " hundred" + (" " + words_positive(value % 100) if value % 100 else "")
    if value < 100000:
        return words_positive(value // 1000) + " thousand" + (" " + words_positive(value % 1000) if value % 1000 else "")
    raise ValueError(value)


def number_words(value: int) -> str:
    return ("negative " if value < 0 else "") + words_positive(abs(value))


def place_value(value: int) -> str:
    digits = str(abs(value))
    labels = []
    for offset, digit in enumerate(reversed(digits)):
        labels.append(f"{PLACES[offset]} digit {DIGIT_WORDS[int(digit)]}")
    annotation = ", ".join(reversed(labels))
    sign = "negative; " if value < 0 else ""
    return f"{value} (place value: {sign}{annotation})"


def transform(prompt: str, variant: str) -> str:
    lines = prompt.splitlines()
    for index, line in enumerate(lines):
        if line.startswith("Problem:"):
            renderer = number_words if variant == "number_words" else place_value
            lines[index] = INTEGER.sub(lambda match: renderer(int(match.group())), line)
            break
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--variant", choices=("number_words", "place_value"), required=True)
    parser.add_argument("--per-surface", type=int)
    args = parser.parse_args()
    rows = [json.loads(line) for line in args.input.read_text().splitlines() if line.strip()]
    if args.per_surface is not None:
        kept = []
        counts: dict[str, int] = defaultdict(int)
        for row in rows:
            if counts[row["surface"]] < args.per_surface:
                kept.append(row)
                counts[row["surface"]] += 1
        rows = kept
    transformed = [{**row, "prompt": transform(row["prompt"], args.variant)} for row in rows]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in transformed))
    print(json.dumps({"variant": args.variant, "rows": len(transformed), "output": str(args.output)}, indent=2))


if __name__ == "__main__":
    main()
