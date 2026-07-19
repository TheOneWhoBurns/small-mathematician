#!/usr/bin/env python3
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path


HERE = Path(__file__).resolve().parent
CONTRAST = HERE.parent / "contrast.jsonl"
JUDGMENTS = HERE / "judgments.jsonl"
MANIFEST = HERE / "manifest.json"
SEAL = HERE / "SHA256SUMS.blind"

ROUTES = {
    "polynomial_value_obstruction": "congruence/difference preservation for integer polynomial values",
    "diophantine_solvability": "gcd divisibility criterion for integer linear equations",
    "modular_period_prime_filter": "periodicity of modular powers used to filter primes",
    "finite_double_count": "count the same finite incidences/objects in two ways",
    "finite_recurrence_period": "finite-state repetition/cycle detection for recurrences",
}

# This is the sole recognizable proposal under the supplied definitions. The
# response itself explicitly proposes repetition plus modular arithmetic for an
# iterated pair transformation. All other responses are empty, corrupted,
# reproduce instructions/problem fragments, or name methods without proposing
# one of the five supplied mechanisms precisely enough.
RECOGNIZABLE = {
    "mrc-v1-24-0-cb13ee06ed-b": (
        "finite_recurrence_period",
        "Explicitly proposes repetition with modular arithmetic for an iterated pair transformation, i.e. finite-state cycle detection for a recurrence.",
    ),
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


rows = [json.loads(line) for line in CONTRAST.read_text().splitlines() if line.strip()]
assert len(rows) == 100
assert len({row["id"] for row in rows}) == 100

with JUDGMENTS.open("w", encoding="utf-8") as out:
    for row in rows:
        if row["id"] in RECOGNIZABLE:
            judgment, rationale = RECOGNIZABLE[row["id"]]
            recognizable = True
        else:
            judgment = "ambiguous/missing"
            rationale = "Response text does not clearly propose any one of the five supplied route mechanisms."
            recognizable = False
        out.write(json.dumps({
            "id": row["id"],
            "judgment": judgment,
            "recognizable_route": recognizable,
            "rationale": rationale,
        }, ensure_ascii=False, sort_keys=True) + "\n")

manifest = {
    "audit": "fresh blind semantic route audit",
    "sealed_at_utc": datetime.now(timezone.utc).isoformat(),
    "input": str(CONTRAST.relative_to(HERE.parents[3])),
    "input_sha256": sha256(CONTRAST),
    "records": len(rows),
    "recognizable_route_records": len(RECOGNIZABLE),
    "ambiguous_or_missing_records": len(rows) - len(RECOGNIZABLE),
    "allowed_route_definitions": ROUTES,
    "blindness_statement": (
        "Before sealing, the auditor read only contrast.jsonl and the five route definitions supplied in the task. "
        "No prompts, gold labels, other runs, prior audits, reports, or evaluations were opened. Judgments use response text alone."
    ),
    "judgment_policy": (
        "Classify only a route actually proposed by the response text. Do not infer from ID, repair the response, or solve the underlying problem; otherwise mark ambiguous/missing."
    ),
}
MANIFEST.write_text(json.dumps(manifest, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")

SEAL.write_text(
    f"{sha256(JUDGMENTS)}  {JUDGMENTS.name}\n"
    f"{sha256(MANIFEST)}  {MANIFEST.name}\n",
    encoding="ascii",
)
print(SEAL.read_text(), end="")
