#!/usr/bin/env python3
"""Fetch pinned bootstrap assets without relying on mutable branch heads."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import sys
import tempfile
import urllib.error
import urllib.request
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LOCK_PATH = ROOT / "assets" / "sources.lock.json"
MODEL_ROOT = ROOT / "assets" / "models" / "qwen3-0.6b-base"
RAW_ROOT = ROOT / "assets" / "data" / "raw"


def hf_url(repo_kind: str, repo: str, revision: str, path: str) -> str:
    prefix = "datasets/" if repo_kind == "dataset" else ""
    return f"https://huggingface.co/{prefix}{repo}/resolve/{revision}/{path}?download=true"


def digest(path: Path, algorithm: str) -> str:
    hasher = hashlib.new(algorithm)
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(8 * 1024 * 1024), b""):
            hasher.update(chunk)
    return hasher.hexdigest()


def validate(path: Path, spec: dict[str, object]) -> None:
    expected_size = int(spec["size"])
    if path.stat().st_size != expected_size:
        raise ValueError(
            f"size mismatch for {path}: {path.stat().st_size} != {expected_size}"
        )
    for algorithm in ("sha256", "md5"):
        expected = spec.get(algorithm)
        if expected and digest(path, algorithm) != expected:
            raise ValueError(f"{algorithm} mismatch for {path}")


def download(url: str, destination: Path, spec: dict[str, object]) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    if destination.exists():
        try:
            validate(destination, spec)
            print(f"ok       {destination.relative_to(ROOT)}")
            return
        except ValueError:
            destination.unlink()

    with tempfile.NamedTemporaryFile(
        dir=destination.parent, prefix=f".{destination.name}.", delete=False
    ) as temp:
        temp_path = Path(temp.name)
    try:
        request = urllib.request.Request(url, headers={"User-Agent": "small-mathematician-bootstrap/1"})
        with urllib.request.urlopen(request, timeout=120) as response, temp_path.open("wb") as output:
            shutil.copyfileobj(response, output, length=8 * 1024 * 1024)
        validate(temp_path, spec)
        os.replace(temp_path, destination)
        print(f"fetched  {destination.relative_to(ROOT)}")
    except (OSError, urllib.error.URLError, ValueError):
        temp_path.unlink(missing_ok=True)
        raise


def source_files(
    lock: dict[str, object], include_model: bool, include_datasets: bool = True
) -> list[tuple[str, Path, dict[str, object]]]:
    sources = lock["sources"]
    jobs: list[tuple[str, Path, dict[str, object]]] = []

    model = sources["qwen3_0_6b_base"]
    if include_model:
        for spec in model["files"]:
            jobs.append(
                (
                    hf_url("model", model["repository"], model["revision"], spec["path"]),
                    MODEL_ROOT / spec["path"],
                    spec,
                )
            )

    if include_datasets:
        naturalproofs = sources["naturalproofs_2"]
        for spec in naturalproofs["files"]:
            jobs.append(
                (
                    f"https://zenodo.org/api/records/4902289/files/{spec['path']}/content",
                    RAW_ROOT / "naturalproofs" / spec["path"],
                    spec,
                )
            )

    if include_datasets:
        for key, folder in (
            ("fineproofs_sft", "fineproofs"),
            ("proofbench", "proofbench"),
            ("ma_proofbench", "ma-proofbench"),
        ):
            source = sources[key]
            for spec in source["files"]:
                jobs.append(
                    (
                        hf_url("dataset", source["repository"], source["revision"], spec["path"]),
                        RAW_ROOT / folder / spec["path"],
                        spec,
                    )
                )
    return jobs


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--without-model",
        action="store_true",
        help="fetch only datasets; useful for refreshing data without the 1.2 GB model",
    )
    parser.add_argument(
        "--only",
        choices=("all", "model", "datasets"),
        default="all",
        help="fetch only the pinned model or datasets instead of the full bootstrap set",
    )
    args = parser.parse_args()
    if args.without_model and args.only != "all":
        parser.error("--without-model cannot be combined with --only")
    lock = json.loads(LOCK_PATH.read_text())
    include_model = not args.without_model and args.only in ("all", "model")
    include_datasets = args.only in ("all", "datasets")
    jobs = source_files(
        lock, include_model=include_model, include_datasets=include_datasets
    )
    print(f"Fetching {len(jobs)} pinned files")
    for url, destination, spec in jobs:
        download(url, destination, spec)
    return 0


if __name__ == "__main__":
    sys.exit(main())
