#!/usr/bin/env python3
"""Restore hash-pinned small-mathematician artifacts on demand."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MANIFEST_PATH = ROOT / "artifacts" / "manifest.json"


def digest(path: Path) -> str:
    hasher = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(8 * 1024 * 1024), b""):
            hasher.update(chunk)
    return hasher.hexdigest()


def validate(path: Path, spec: dict[str, object]) -> None:
    if not path.is_file():
        raise FileNotFoundError(path)
    if path.stat().st_size != int(spec["bytes"]):
        raise ValueError(f"size mismatch for {path}")
    actual = digest(path)
    if actual != spec["sha256"]:
        raise ValueError(f"sha256 mismatch for {path}: {actual}")


def project_path(relative: str) -> Path:
    result = (ROOT / relative).resolve()
    if ROOT.resolve() not in result.parents:
        raise ValueError(f"artifact path escapes project: {relative}")
    return result


def require_gh() -> None:
    if not shutil.which("gh"):
        raise SystemExit("GitHub CLI is required: https://cli.github.com/")
    subprocess.run(
        ["gh", "auth", "status", "--hostname", "github.com"],
        check=True,
        stdout=subprocess.DEVNULL,
    )


def fetch_release_artifact(
    repository: str, tag: str, artifact_id: str, spec: dict[str, object], force: bool
) -> None:
    destination = project_path(str(spec["destination"]))
    try:
        validate(destination, spec)
        print(f"ok       {artifact_id}: {destination.relative_to(ROOT)}")
        return
    except (FileNotFoundError, ValueError) as error:
        if destination.exists() and not force:
            raise SystemExit(f"{error}; pass --force to replace it") from error

    require_gh()
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=destination.parent, prefix=".hydrate-") as temp:
        temp_dir = Path(temp)
        subprocess.run(
            [
                "gh",
                "release",
                "download",
                tag,
                "--repo",
                repository,
                "--pattern",
                str(spec["release_asset"]),
                "--dir",
                str(temp_dir),
            ],
            check=True,
        )
        downloaded = temp_dir / str(spec["release_asset"])
        validate(downloaded, spec)
        os.replace(downloaded, destination)
    print(f"fetched  {artifact_id}: {destination.relative_to(ROOT)}")


def main() -> None:
    manifest = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    parser = argparse.ArgumentParser()
    parser.add_argument("--profile", choices=sorted(manifest["profiles"]))
    parser.add_argument("--artifact", action="append", choices=sorted(manifest["artifacts"]), default=[])
    parser.add_argument("--verify-only", action="store_true")
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    if not args.profile and not args.artifact:
        parser.error("choose --profile or at least one --artifact")

    external_ids: list[str] = []
    artifact_ids = list(args.artifact)
    if args.profile:
        profile = manifest["profiles"][args.profile]
        external_ids.extend(profile["external_sources"])
        artifact_ids.extend(profile["artifacts"])
    external_ids = list(dict.fromkeys(external_ids))
    artifact_ids = list(dict.fromkeys(artifact_ids))

    if args.verify_only:
        for artifact_id in artifact_ids:
            spec = manifest["artifacts"][artifact_id]
            validate(project_path(spec["destination"]), spec)
            print(f"verified {artifact_id}")
        return

    for source_id in external_ids:
        source = manifest["external_sources"][source_id]
        command = list(source["fetch_command"])
        command[0] = str(Path(os.sys.executable))
        subprocess.run(command, cwd=ROOT, check=True)
    for artifact_id in artifact_ids:
        fetch_release_artifact(
            manifest["repository"],
            manifest["release_tag"],
            artifact_id,
            manifest["artifacts"][artifact_id],
            args.force,
        )


if __name__ == "__main__":
    main()
