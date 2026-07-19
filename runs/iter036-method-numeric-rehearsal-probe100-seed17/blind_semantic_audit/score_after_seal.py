#!/usr/bin/env python3
import hashlib
import json
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PROMPTS = ROOT / "benchmarks/method_router/contrast/data/prompts.jsonl"
JUDGMENTS = HERE / "judgments.jsonl"
MANIFEST = HERE / "manifest.json"
BLIND_SEAL = HERE / "SHA256SUMS.blind"
REPORT = HERE / "report.json"
REPORT_SEAL = HERE / "SHA256SUMS.report"


def load_jsonl(path: Path):
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


prompts = load_jsonl(PROMPTS)
judgments = load_jsonl(JUDGMENTS)
assert len(prompts) == len(judgments) == 100
gold = {row["id"]: row for row in prompts}
pred = {row["id"]: row for row in judgments}
assert gold.keys() == pred.keys()

correct = {item_id: pred[item_id]["judgment"] == gold[item_id]["route"] for item_id in gold}
route_totals = Counter(row["route"] for row in prompts)
route_correct = Counter(gold[item_id]["route"] for item_id, ok in correct.items() if ok)

pair_members = defaultdict(list)
for row in prompts:
    pair_members[row["pair_id"]].append(row["id"])
assert len(pair_members) == 50
assert all(len(members) == 2 for members in pair_members.values())
pair_correct = {
    pair_id: all(correct[item_id] for item_id in members)
    for pair_id, members in pair_members.items()
}

recognizable = [row for row in judgments if row["recognizable_route"]]
recognizable_correct = sum(correct[row["id"]] for row in recognizable)

per_route = {}
for route in sorted(route_totals):
    total = route_totals[route]
    n_correct = route_correct[route]
    per_route[route] = {
        "correct": n_correct,
        "total": total,
        "accuracy": n_correct / total,
    }

blind_seal_lines = BLIND_SEAL.read_text().splitlines()
blind_hashes = {line.split(maxsplit=1)[1]: line.split(maxsplit=1)[0] for line in blind_seal_lines}

report = {
    "scored_at_utc": datetime.now(timezone.utc).isoformat(),
    "join_key": "id",
    "gold_source": str(PROMPTS.relative_to(ROOT)),
    "gold_source_sha256": sha256(PROMPTS),
    "blind_artifacts": {
        "judgments_sha256": blind_hashes["judgments.jsonl"],
        "manifest_sha256": blind_hashes["manifest.json"],
        "seal_sha256": sha256(BLIND_SEAL),
        "seal_verified_before_gold_open": True,
    },
    "metrics": {
        "overall_accuracy": {
            "correct": sum(correct.values()),
            "total": len(correct),
            "accuracy": sum(correct.values()) / len(correct),
        },
        "per_route_accuracy": per_route,
        "matched_pair_accuracy": {
            "definition": "A matched pair is correct only if both of its two response judgments equal their gold routes.",
            "correct": sum(pair_correct.values()),
            "total": len(pair_correct),
            "accuracy": sum(pair_correct.values()) / len(pair_correct),
        },
        "recognizable_route_precision": {
            "definition": "Correct gold-route matches divided by judgments marked recognizable_route=true.",
            "correct": recognizable_correct,
            "total": len(recognizable),
            "precision": recognizable_correct / len(recognizable) if recognizable else None,
        },
        "recognizable_route_coverage": {
            "recognizable": len(recognizable),
            "total": len(judgments),
            "coverage": len(recognizable) / len(judgments),
        },
    },
    "recognizable_judgments": [
        {
            "id": row["id"],
            "judgment": row["judgment"],
            "gold_route": gold[row["id"]]["route"],
            "correct": correct[row["id"]],
        }
        for row in recognizable
    ],
    "limitations": [
        "The audit is intentionally strict and response-text-only; corrupted, truncated, instruction-echoing, or underspecified text is not repaired from the prompt.",
        "Ambiguous/missing is treated as incorrect for accuracy and excluded from the denominator of recognizable-route precision.",
        "Recognizable-route precision has a denominator of one, so its 100% estimate is statistically uninformative by itself.",
        "Matched-pair accuracy uses the strict both-sides-correct definition.",
    ],
}
REPORT.write_text(json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
REPORT_SEAL.write_text(f"{sha256(REPORT)}  {REPORT.name}\n", encoding="ascii")
print(json.dumps(report["metrics"], indent=2, sort_keys=True))
print(REPORT_SEAL.read_text(), end="")
