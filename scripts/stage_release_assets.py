#!/usr/bin/env python3
"""Create zero-copy hard links with unique GitHub Release asset names."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path

from hydrate import MANIFEST_PATH, ROOT, project_path, validate


def main() -> None:
    manifest = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact", action="append", choices=sorted(manifest["artifacts"]), default=[])
    parser.add_argument("--clean", action="store_true")
    args = parser.parse_args()
    staging = ROOT / ".release-staging"
    artifact_ids = args.artifact or list(manifest["artifacts"])
    if args.clean:
        if staging.exists():
            for path in staging.iterdir():
                if path.is_file():
                    path.unlink()
            staging.rmdir()
        print(json.dumps({"cleaned": str(staging)}))
        return
    staging.mkdir(exist_ok=True)
    staged = []
    for artifact_id in artifact_ids:
        spec = manifest["artifacts"][artifact_id]
        source = project_path(spec["destination"])
        validate(source, spec)
        destination = staging / spec["release_asset"]
        if destination.exists():
            if not destination.samefile(source):
                raise SystemExit(f"staging collision: {destination}")
        else:
            os.link(source, destination)
        staged.append({"id": artifact_id, "path": str(destination), "bytes": spec["bytes"], "sha256": spec["sha256"]})
    print(json.dumps({"staged": staged}, indent=2))


if __name__ == "__main__":
    main()
