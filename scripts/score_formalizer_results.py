#!/usr/bin/env python3
"""Validate and score paired outcomes from a frozen formalizer experiment."""

from __future__ import annotations

import argparse
import hashlib
import json
import random
from collections import defaultdict
from pathlib import Path
from typing import Any


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--outcomes", type=Path)
    parser.add_argument("--check-config", action="store_true")
    return parser.parse_args()


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    with path.open() as handle:
        return [json.loads(line) for line in handle if line.strip()]


def validate_config(config: dict[str, Any], root: Path) -> None:
    if config["status"] not in {
        "frozen_design_pending_formalizer_binding",
        "frozen_formalizer_bound",
    }:
        raise ValueError("experiment status is not a recognized frozen state")
    model = config["model"]
    if model["parameter_count"] != 596_049_920:
        raise ValueError("unexpected Qwen3-0.6B parameter count")
    candidate = root / config["data"]["candidate_pool"]
    if not candidate.is_file():
        raise FileNotFoundError(candidate)
    forbidden = ("/eval/", "/verifier-only/")
    candidate_text = "/" + str(candidate.resolve()).replace("\\", "/") + "/"
    if any(marker in candidate_text for marker in forbidden):
        raise ValueError("candidate pool crosses the sealed-evaluation boundary")
    for path in config["data"]["sealed_final_benchmarks"]:
        if not (root / path).is_file():
            raise FileNotFoundError(root / path)


def clustered_interval(
    units: list[dict[str, Any]],
    first: str,
    second: str,
    *,
    samples: int = 10_000,
    seed: int = 20_260_719,
) -> tuple[float, float]:
    by_family: dict[str, list[float]] = defaultdict(list)
    for unit in units:
        by_family[unit["family_id"]].append(unit[first] - unit[second])
    families = sorted(by_family)
    rng = random.Random(seed)
    draws: list[float] = []
    for _ in range(samples):
        values: list[float] = []
        for _family in families:
            picked = families[rng.randrange(len(families))]
            values.extend(by_family[picked])
        draws.append(sum(values) / len(values))
    draws.sort()
    return draws[int(0.025 * samples)], draws[int(0.975 * samples)]


def main() -> None:
    args = parse_args()
    config = json.loads(args.config.read_text())
    root = args.config.resolve().parents[1]
    validate_config(config, root)
    config_sha = hashlib.sha256(args.config.read_bytes()).hexdigest()
    if args.check_config and args.outcomes is None:
        print(json.dumps({"config": str(args.config), "sha256": config_sha, "valid": True}, indent=2))
        return
    if args.outcomes is None:
        raise ValueError("--outcomes is required unless --check-config is used")
    if config["status"] != "frozen_formalizer_bound":
        raise ValueError("scientific scoring is blocked until the formalizer is bound in config")

    rows = read_jsonl(args.outcomes)
    required = config["scientific_evaluation"]["required_conditions"]
    fields = {
        "theorem_id",
        "family_id",
        "generation_seed",
        "condition",
        "statement_faithful",
        "lean_verified",
    }
    grouped: dict[tuple[str, int], dict[str, dict[str, Any]]] = defaultdict(dict)
    for row in rows:
        missing = fields - row.keys()
        if missing:
            raise ValueError(f"outcome missing fields {sorted(missing)}")
        key = (row["theorem_id"], int(row["generation_seed"]))
        condition = row["condition"]
        if condition in grouped[key]:
            raise ValueError(f"duplicate condition {condition} for {key}")
        grouped[key][condition] = row

    units: list[dict[str, Any]] = []
    for key, conditions in sorted(grouped.items()):
        missing = set(required) - conditions.keys()
        extra = conditions.keys() - set(required)
        if missing or extra:
            raise ValueError(f"condition mismatch for {key}: missing={sorted(missing)}, extra={sorted(extra)}")
        families = {row["family_id"] for row in conditions.values()}
        if len(families) != 1:
            raise ValueError(f"family_id mismatch for {key}")
        unit: dict[str, Any] = {"theorem_id": key[0], "seed": key[1], "family_id": families.pop()}
        for condition, row in conditions.items():
            unit[condition] = int(bool(row["statement_faithful"]) and bool(row["lean_verified"]))
        units.append(unit)

    if not units:
        raise ValueError("no complete paired units")
    rates = {
        condition: sum(unit[condition] for unit in units) / len(units)
        for condition in required
    }
    uplift = rates["model_blueprint"] - rates["no_blueprint"]
    interval = clustered_interval(units, "model_blueprint", "no_blueprint")
    helped = sum(u["model_blueprint"] == 1 and u["no_blueprint"] == 0 for u in units)
    harmed = sum(u["model_blueprint"] == 0 and u["no_blueprint"] == 1 for u in units)
    result = {
        "config_sha256": config_sha,
        "outcomes_sha256": hashlib.sha256(args.outcomes.read_bytes()).hexdigest(),
        "paired_units": len(units),
        "families": len({u["family_id"] for u in units}),
        "faithful_verified_solve_rates": rates,
        "primary_uplift_percentage_points": 100 * uplift,
        "primary_uplift_95pct_family_cluster_bootstrap_pp": [100 * interval[0], 100 * interval[1]],
        "paired_helped": helped,
        "paired_harmed": harmed,
        "control_deltas_percentage_points": {
            "model_minus_corrupted": 100 * (rates["model_blueprint"] - rates["corrupted_blueprint"]),
            "model_minus_generic": 100 * (rates["model_blueprint"] - rates["generic_blueprint"]),
            "trained_minus_base_model": 100 * (rates["model_blueprint"] - rates["base_model_blueprint"]),
            "reference_ceiling_minus_model": 100 * (rates["reference_argument"] - rates["model_blueprint"]),
        },
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
