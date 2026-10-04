#!/usr/bin/env python3
"""Install the pinned official Verus release locally; never change rustup defaults."""

import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parent.parent
LOCK = json.loads((ROOT / "toolchain.lock.json").read_text())


def platform_key():
    host = (platform.system(), platform.machine().lower())
    supported = {
        ("Darwin", "arm64"): "arm64-macos",
        ("Darwin", "aarch64"): "arm64-macos",
        ("Darwin", "x86_64"): "x86-macos",
        ("Linux", "x86_64"): "x86-linux",
        ("Linux", "amd64"): "x86-linux",
    }
    if host not in supported:
        sys.exit(f"No pinned official Verus release for {host}; see toolchain.lock.json")
    return supported[host]


def run(*args):
    subprocess.run([str(arg) for arg in args], check=True)


def digest(path):
    hasher = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            hasher.update(chunk)
    return hasher.hexdigest()


def main():
    asset = LOCK["verus"]["assets"][platform_key()]
    tools = ROOT / ".tools"
    downloads = tools / "downloads"
    downloads.mkdir(parents=True, exist_ok=True)
    archive = downloads / asset["archive"]
    destination = tools / asset["directory"]
    stamp = destination / ".cordis-sha256"

    if not (stamp.is_file() and stamp.read_text().strip() == asset["sha256"]):
        if not archive.exists():
            partial = archive.with_suffix(".zip.partial")
            run("curl", "--fail", "--location", "--retry", "3", "--output", partial, asset["url"])
            partial.replace(archive)
        actual = digest(archive)
        if actual != asset["sha256"]:
            sys.exit(f"Checksum mismatch for {archive}: {actual}; remove this archive and retry")
        with tempfile.TemporaryDirectory(prefix="verus-extract-", dir=tools) as staging:
            staging = Path(staging)
            with zipfile.ZipFile(archive) as bundle:
                for entry in bundle.infolist():
                    target = (staging / entry.filename).resolve()
                    if not target.is_relative_to(staging.resolve()):
                        sys.exit("Refusing archive entry outside extraction directory")
                bundle.extractall(staging)
                for entry in bundle.infolist():
                    permissions = (entry.external_attr >> 16) & 0o777
                    if permissions:
                        (staging / entry.filename).chmod(permissions)
            extracted = staging / asset["directory"]
            if not (extracted / "verus").is_file():
                sys.exit("Pinned archive did not contain the expected Verus binary")
            if destination.exists():
                shutil.rmtree(destination)
            extracted.rename(destination)
        stamp.write_text(asset["sha256"] + "\n")

    cargo_bin = Path(os.environ.get("CARGO_HOME", str(Path.home() / ".cargo"))) / "bin"
    os.environ["PATH"] = str(cargo_bin) + os.pathsep + os.environ.get("PATH", "")
    rustup = shutil.which("rustup")
    if rustup is None:
        sys.exit("Install rustup from https://rustup.rs, then rerun scripts/install-verus.sh")
    rust = LOCK["rust"]
    command = [rustup, "toolchain", "install", rust["channel"], "--profile", rust["profile"], "--no-self-update"]
    for component in rust["components"]:
        command += ["--component", component]
    run(*command)
    os.environ["RUSTUP_TOOLCHAIN"] = rust["channel"]
    run(destination / "verus", "--version")
    print(f"Installed and checksum-verified {destination.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
