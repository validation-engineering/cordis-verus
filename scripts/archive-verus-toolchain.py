#!/usr/bin/env python3
"""Recover checksum-locked Verus release ZIPs from their original Actions run.

This maintainer tool only reads GitHub and writes local files. Publishing the
resulting toolchain archive is a separate workflow step, never a runtime release.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parent.parent


class RecoveryError(RuntimeError):
    """Recovery evidence or archive bytes did not match the pinned inputs."""


def file_digest(path):
    hasher = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            hasher.update(chunk)
    return hasher.hexdigest()


def github_json(endpoint):
    result = subprocess.run(["gh", "api", "--hostname", "github.com", endpoint],
                            check=True, capture_output=True, text=True)
    return json.loads(result.stdout)


def download_artifact(repository, artifact_id, destination):
    endpoint = f"repos/{repository}/actions/artifacts/{artifact_id}/zip"
    with destination.open("wb") as output:
        subprocess.run(["gh", "api", "--hostname", "github.com", endpoint],
                       check=True, stdout=output)


def validate_manifest(manifest, lock):
    if manifest.get("schema_version") != 1:
        raise RecoveryError("Unsupported toolchain recovery manifest schema")
    if manifest.get("repository") != "verus-lang/verus":
        raise RecoveryError("Recovery must use the official verus-lang/verus repository")
    if manifest.get("commit") != lock["verus"]["commit"]:
        raise RecoveryError("Recovery commit does not match toolchain.lock.json")
    if not isinstance(manifest.get("run_id"), int) or manifest["run_id"] <= 0:
        raise RecoveryError("Recovery manifest requires a positive Actions run ID")
    artifacts = manifest.get("artifacts", {})
    if set(artifacts) != set(lock["verus"]["assets"]):
        raise RecoveryError("Recovery manifest must cover exactly the locked platforms")
    artifact_ids = set()
    for platform, entry in artifacts.items():
        artifact_id = entry.get("id")
        if not isinstance(artifact_id, int) or artifact_id <= 0 or artifact_id in artifact_ids:
            raise RecoveryError("Recovery artifact IDs must be positive and unique")
        artifact_ids.add(artifact_id)
        if not isinstance(entry.get("name"), str) or not entry["name"]:
            raise RecoveryError(f"Recovery artifact name is missing for {platform}")
        if entry.get("member") != f"verus-{platform}.zip":
            raise RecoveryError(f"Recovery must select the exact original ZIP member for {platform}")
        archive = lock["verus"]["assets"][platform]["archive"]
        if Path(archive).name != archive or "\\" in archive:
            raise RecoveryError("Locked archive must be a plain filename")


def validate_run(run, manifest):
    if (run.get("id") != manifest["run_id"]
            or run.get("head_sha") != manifest["commit"]
            or run.get("repository", {}).get("full_name") != manifest["repository"]):
        raise RecoveryError("Actions run identity does not match the recovery manifest")
    if run.get("status") != "completed" or run.get("conclusion") != "success":
        raise RecoveryError("Original Verus Actions run must have completed successfully")


def validate_artifact(artifact, expected, manifest):
    if artifact.get("id") != expected["id"] or artifact.get("name") != expected["name"]:
        raise RecoveryError("Actions artifact identity does not match the recovery manifest")
    if artifact.get("expired") is not False:
        raise RecoveryError("Original Verus Actions artifact has expired or expiry is unknown")
    run = artifact.get("workflow_run", {})
    if run.get("id") != manifest["run_id"] or run.get("head_sha") != manifest["commit"]:
        raise RecoveryError("Actions artifact does not belong to the pinned Verus run and commit")


def recover_member(wrapper, member, destination, expected_sha256):
    """Stream only the named ZIP member; publish bytes only after hash validation."""
    hasher = hashlib.sha256()
    size = 0
    partial = destination.with_suffix(destination.suffix + ".partial")
    try:
        with zipfile.ZipFile(wrapper) as bundle:
            matches = [entry for entry in bundle.infolist() if entry.filename == member]
            if len(matches) != 1:
                raise RecoveryError(f"Artifact must contain exactly one {member}")
            entry = matches[0]
            if entry.is_dir() or stat.S_IFMT(entry.external_attr >> 16) not in (0, stat.S_IFREG):
                raise RecoveryError("Selected Verus archive member must be a regular file")
            with bundle.open(entry) as source, partial.open("wb") as output:
                for chunk in iter(lambda: source.read(1024 * 1024), b""):
                    hasher.update(chunk)
                    size += len(chunk)
                    output.write(chunk)
        actual = hasher.hexdigest()
        if actual != expected_sha256:
            raise RecoveryError(f"Recovered {member} checksum mismatch: expected {expected_sha256}, got {actual}")
        partial.replace(destination)
        return size
    finally:
        partial.unlink(missing_ok=True)


def recover_platform(platform, expected, asset, manifest, staging):
    repository = manifest["repository"]
    artifact = github_json(f"repos/{repository}/actions/artifacts/{expected['id']}")
    validate_artifact(artifact, expected, manifest)
    directory = staging / platform
    directory.mkdir()
    wrapper = directory / "actions-artifact.zip"
    download_artifact(repository, expected["id"], wrapper)
    destination = directory / asset["archive"]
    size = recover_member(wrapper, expected["member"], destination, asset["sha256"])
    result = {
        "id": expected["id"],
        "name": expected["name"],
        "member": expected["member"],
        "archive": asset["archive"],
        "sha256": asset["sha256"],
        "bytes": size,
        "actions_zip_sha256": file_digest(wrapper),
        "created_at": artifact.get("created_at"),
        "expires_at": artifact.get("expires_at"),
        "artifact_digest": artifact.get("digest"),
    }
    wrapper.unlink()
    print(f"Verified {platform}: {asset['archive']} ({size} bytes)", flush=True)
    return platform, destination, result


def require_new_output(output):
    if output.exists() or output.is_symlink():
        raise RecoveryError(f"Recovery output already exists; choose a new directory: {output}")


def recover(manifest, lock, output, jobs=3):
    require_new_output(output)
    validate_manifest(manifest, lock)
    repository = manifest["repository"]
    run = github_json(f"repos/{repository}/actions/runs/{manifest['run_id']}")
    validate_run(run, manifest)
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="verus-recovery-", dir=output.parent) as directory:
        staging = Path(directory)
        with ThreadPoolExecutor(max_workers=jobs) as workers:
            futures = [workers.submit(recover_platform, platform, expected,
                                      lock["verus"]["assets"][platform], manifest, staging)
                       for platform, expected in sorted(manifest["artifacts"].items())]
            results = [future.result() for future in futures]
        provenance = {
            "schema_version": 1,
            "kind": "verus-toolchain-recovery",
            "recovered_at": datetime.now(timezone.utc).isoformat(),
            "repository": repository,
            "run_id": manifest["run_id"],
            "run_url": f"https://github.com/{repository}/actions/runs/{manifest['run_id']}",
            "commit": manifest["commit"],
            "verus_version": lock["verus"]["version"],
            "artifacts": {platform: evidence for platform, _, evidence in results},
        }
        complete = staging / "complete"
        complete.mkdir()
        for _, archive, _ in results:
            archive.replace(complete / archive.name)
        (complete / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
        require_new_output(output)
        complete.rename(output)
    return provenance


def main():
    lock = json.loads((ROOT / "toolchain.lock.json").read_text())
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--metadata", type=Path,
                        default=ROOT / "docs/toolchains" / f"verus-{lock['verus']['version']}.json")
    parser.add_argument("--output", type=Path, default=ROOT / "target/toolchain-archive",
                        help="New output directory; an existing path is never reused")
    parser.add_argument("--jobs", type=int, choices=range(1, 4), default=3)
    arguments = parser.parse_args()
    if shutil.which("gh") is None:
        raise RecoveryError("Install GitHub CLI and authenticate to read the original Actions artifacts")
    manifest = json.loads(arguments.metadata.read_text())
    recover(manifest, lock, arguments.output, arguments.jobs)
    print(f"Recovered all locked Verus platforms to {arguments.output}")


if __name__ == "__main__":
    try:
        main()
    except (RecoveryError, OSError, subprocess.CalledProcessError, zipfile.BadZipFile,
            json.JSONDecodeError) as error:
        sys.exit(str(error))
