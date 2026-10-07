#!/usr/bin/env python3
"""Install the pinned official Verus release locally; never change rustup defaults."""

import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import stat
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


class InstallError(RuntimeError):
    """No verified toolchain could be installed; existing files remain usable."""


def download_api_asset(endpoint, partial):
    # This fixed GitHub endpoint reads release bytes; no token enters arguments or logs.
    if not re.fullmatch(r"repos/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+/releases/assets/[1-9][0-9]*", endpoint):
        raise InstallError("Invalid GitHub release asset API endpoint in toolchain lock")
    gh = shutil.which("gh")
    if gh is None:
        raise InstallError("Private toolchain mirror requires GitHub CLI (gh) and read access")
    with partial.open("wb") as output:
        subprocess.run([gh, "api", "--hostname", "github.com", "-H",
                        "Accept: application/octet-stream", endpoint], check=True, stdout=output)


def ensure_archive(asset, downloads):
    """Cache only hash-verified bytes, trying the durable mirror before upstream."""
    downloads.mkdir(parents=True, exist_ok=True)
    archive = downloads / asset["archive"]
    if archive.is_file() and digest(archive) == asset["sha256"]:
        return archive

    sources = []
    if asset.get("mirror_api"):
        sources.append(("api", asset["mirror_api"]))
    sources.extend(("url", url) for url in dict.fromkeys(
        url for url in (asset.get("mirror_url"), asset["url"]) if url
    ))
    failures = []
    with tempfile.TemporaryDirectory(prefix="verus-download-", dir=downloads) as staging:
        partial = Path(staging) / "archive.zip"
        for transport, source in sources:
            try:
                if transport == "api":
                    download_api_asset(source, partial)
                else:
                    run("curl", "--fail", "--location", "--retry", "3",
                        "--proto", "=https", "--proto-redir", "=https",
                        "--output", partial, source)
                actual = digest(partial)
                if actual != asset["sha256"]:
                    raise InstallError(f"checksum mismatch: expected {asset['sha256']}, got {actual}")
                partial.replace(archive)
                return archive
            except (subprocess.CalledProcessError, OSError, InstallError) as error:
                failures.append(f"{source}: {error}")
                print(f"Verus download failed: {failures[-1]}", file=sys.stderr)
            finally:
                partial.unlink(missing_ok=True)
    raise InstallError("No checksum-verified Verus archive was available:\n" + "\n".join(failures))


def extract_archive(archive, asset, tools):
    """Validate in staging, then replace the installation with rollback on failure."""
    tools.mkdir(parents=True, exist_ok=True)
    destination = tools / asset["directory"]
    with tempfile.TemporaryDirectory(prefix="verus-extract-", dir=tools) as staging:
        staging = Path(staging)
        with zipfile.ZipFile(archive) as bundle:
            seen = set()
            for entry in bundle.infolist():
                target = (staging / entry.filename).resolve()
                if not target.is_relative_to(staging.resolve()) or "\\" in entry.filename:
                    raise InstallError("Refusing archive entry outside extraction directory")
                if target in seen:
                    raise InstallError("Refusing duplicate archive entry")
                seen.add(target)
                kind = stat.S_IFMT(entry.external_attr >> 16)
                if kind not in (0, stat.S_IFREG, stat.S_IFDIR):
                    raise InstallError("Refusing archive link or special file")
            bundle.extractall(staging)
            for entry in bundle.infolist():
                permissions = (entry.external_attr >> 16) & 0o777
                if permissions:
                    (staging / entry.filename).chmod(permissions)
        extracted = staging / asset["directory"]
        binary = extracted / "verus"
        if not binary.is_file() or not os.access(binary, os.X_OK):
            raise InstallError("Pinned archive did not contain the expected executable Verus binary")
        (extracted / ".cordis-sha256").write_text(asset["sha256"] + "\n")
        # The old installation must survive even if rollback itself is interrupted.
        # Keep its backup outside TemporaryDirectory's automatic cleanup scope.
        backup = None
        previous = None
        if destination.exists() or destination.is_symlink():
            backup = Path(tempfile.mkdtemp(prefix="verus-backup-", dir=tools))
            previous = backup / asset["directory"]
        try:
            if previous is not None:
                destination.rename(previous)
            extracted.rename(destination)
        except BaseException as error:
            if previous is not None and (previous.exists() or previous.is_symlink()):
                try:
                    previous.rename(destination)
                except BaseException:
                    raise InstallError(
                        f"Toolchain replacement failed and automatic rollback failed; "
                        f"the previous installation is preserved at {previous}"
                    ) from error
            if backup is not None:
                backup.rmdir()
            raise
        if backup is not None:
            shutil.rmtree(backup)
    return destination


def install_asset(asset, tools):
    destination = tools / asset["directory"]
    stamp = destination / ".cordis-sha256"
    binary = destination / "verus"
    if (stamp.is_file() and stamp.read_text().strip() == asset["sha256"]
            and binary.is_file() and os.access(binary, os.X_OK)):
        return destination
    archive = ensure_archive(asset, tools / "downloads")
    return extract_archive(archive, asset, tools)


def main():
    asset = LOCK["verus"]["assets"][platform_key()]
    destination = install_asset(asset, ROOT / ".tools")

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
    try:
        main()
    except (InstallError, zipfile.BadZipFile) as error:
        sys.exit(str(error))
