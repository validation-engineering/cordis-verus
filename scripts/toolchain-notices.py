#!/usr/bin/env python3
"""Preserve pinned Verus source and vendored Cargo dependency notices for review.

This supplements byte-for-byte upstream toolchain archives. It is not a license
audit, a complete binary SBOM, or a claim that the binaries can be rebuilt from
this directory alone. The caller may archive the resulting directory unchanged.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
import tempfile
from urllib.request import urlopen


ROOT = Path(__file__).resolve().parent.parent
Z3_URL = "https://raw.githubusercontent.com/Z3Prover/z3/ddb49568d3520e99799e364fb22f35fc67d887b1/LICENSE.txt"
Z3_SHA256 = "e617cad2ab9347e3129c2b171e87909332174e17961c5c3412d0799469111337"
NOTICE_PREFIXES = ("LICENSE", "LICENCE", "COPYRIGHT", "NOTICE", "AUTHORS", "COPYING", "UNLICENSE")


def command(args, cwd=None, env=None):
    return subprocess.run(args, cwd=cwd, env=env, check=True, text=True,
                          stdout=subprocess.PIPE).stdout


def sha256(filename):
    digest = hashlib.sha256()
    with filename.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def validate_source(source, expected):
    if command(["git", "rev-parse", "--show-toplevel"], cwd=source).strip() != str(source):
        raise ValueError("--source must be the Verus repository root")
    revision = command(["git", "rev-parse", "HEAD"], cwd=source).strip()
    if revision != expected:
        raise ValueError("Verus source HEAD does not match toolchain.lock.json")
    if command(["git", "status", "--porcelain=v1", "--untracked-files=all"], cwd=source).strip():
        raise ValueError("Verus source checkout must be clean")
    entries = command(["git", "ls-tree", "-r", "HEAD"], cwd=source).splitlines()
    if any(entry.startswith("160000 ") for entry in entries):
        raise ValueError("Submodules require explicit source collection; refusing incomplete archive")
    return command(["git", "rev-parse", "HEAD^{tree}"], cwd=source).strip()


def extract_source(archive, destination):
    """Reject links/devices instead of following them outside the staging tree."""
    destination = destination.resolve()
    with tarfile.open(archive, "r") as source_tar:
        members = source_tar.getmembers()
        for member in members:
            resolved = (destination / member.name).resolve()
            if destination not in resolved.parents and resolved != destination:
                raise ValueError("Source archive contains an unsafe path")
            if not (member.isfile() or member.isdir()):
                raise ValueError("Source archive contains an unsupported link or special file")
        source_tar.extractall(destination, members=members)


def notice_files(directory, root, recursive=True):
    candidates = directory.rglob("*") if recursive else directory.iterdir()
    return sorted(str(item.relative_to(root)) for item in candidates
                  if item.is_file() and item.name.upper().startswith(NOTICE_PREFIXES))


def package_record(package, source, stage):
    manifest = Path(package["manifest_path"]).resolve()
    if package["source"] is None:
        try:
            relative = manifest.parent.relative_to(source)
        except ValueError as error:
            raise ValueError("Local dependency lies outside the pinned source checkout") from error
        directory = stage / "verus-source" / relative
        boundary = stage / "verus-source"
    else:
        directory = stage / "vendor" / (package["name"] + "-" + package["version"])
        boundary = directory
    if not (directory / "Cargo.toml").is_file():
        raise ValueError("Missing collected package: " + package["name"])
    notices = notice_files(directory, stage)
    ancestors = []
    parent = directory.parent
    while parent == boundary or boundary in parent.parents:
        ancestors.extend(notice_files(parent, stage, recursive=False))
        if parent == boundary:
            break
        parent = parent.parent
    license_file = package.get("license_file")
    declared_license_file = None
    if license_file:
        original = Path(license_file)
        if not original.is_absolute():
            original = manifest.parent / original
        # A license_file may have a nonstandard name. Preserve it explicitly if
        # Cargo's package copy does not contain it at the same relative location.
        if not original.is_file():
            raise ValueError("Declared license_file is missing for " + package["name"])
        extra = stage / "declared-license-files" / (package["name"] + "-" + package["version"])
        extra.mkdir(parents=True, exist_ok=True)
        copied = extra / original.name
        shutil.copyfile(original, copied)
        declared_license_file = str(copied.relative_to(stage))
    return {
        "name": package["name"], "version": package["version"],
        "license": package.get("license"), "source": package["source"],
        "repository": package.get("repository"), "authors": package.get("authors", []),
        "directory": str(directory.relative_to(stage)),
        "noticeFiles": notices, "ancestorNoticeCandidates": sorted(set(ancestors)),
        "declaredLicenseFile": declared_license_file,
        "missingExplicitNoticeText": not (notices or ancestors or declared_license_file),
    }


def collect(args, lock):
    source, output = args.source.resolve(), args.output.resolve()
    if output.exists():
        raise ValueError("--output already exists; refusing to overwrite it")
    if output == source or source in output.parents:
        raise ValueError("--output must be outside the pinned source checkout")
    expected = lock["verus"]["commit"]
    tree = validate_source(source, expected)
    if not re.fullmatch(r"[0-9a-f]{64}", args.z3_license_sha256):
        raise ValueError("Z3 license SHA256 must be a lowercase 64-digit hash")
    if not args.z3_license_url.startswith("https://"):
        raise ValueError("Z3 license provenance requires an HTTPS URL")
    if args.offline and args.z3_license_file is None:
        raise ValueError("--offline requires --z3-license-file with the pinned license bytes")
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="toolchain-notices-", dir=output.parent) as temporary:
        temporary = Path(temporary)
        stage = temporary / "companion"
        stage.mkdir()
        source_dir = stage / "verus-source"
        source_dir.mkdir()
        archive = temporary / "source.tar"
        subprocess.run(["git", "archive", "--format=tar", "--output", str(archive), expected],
                       cwd=source, check=True)
        extract_source(archive, source_dir)
        env = dict(os.environ, RUSTUP_TOOLCHAIN=lock["rust"]["channel"])
        cargo = args.cargo
        flags = ["--manifest-path", str(source / "source/Cargo.toml"), "--locked"]
        if args.offline:
            flags.append("--offline")
        metadata = json.loads(command([cargo, "metadata", "--format-version", "1"] + flags,
                                      cwd=source, env=env))
        vendor = stage / "vendor"
        config = command([cargo, "vendor", "--versioned-dirs"] + flags + [str(vendor)],
                         cwd=source, env=env)
        # This is a portable configuration fragment, not an installed Cargo
        # configuration. The README explains its directory is relative to use.
        config = config.replace(str(vendor), "vendor")
        (stage / "vendor-config.toml").write_text(config, encoding="utf-8")
        packages = sorted((package_record(package, source, stage) for package in metadata["packages"]),
                          key=lambda package: (package["name"], package["version"], package["source"] or ""))
        licenses = stage / "licenses"
        licenses.mkdir()
        z3_license = licenses / "z3-4.16.0-LICENSE.txt"
        if args.z3_license_file:
            shutil.copyfile(args.z3_license_file, z3_license)
        else:
            with urlopen(args.z3_license_url, timeout=60) as response:
                z3_license.write_bytes(response.read())
        if sha256(z3_license) != args.z3_license_sha256:
            raise ValueError("Z3 license checksum mismatch")
        if validate_source(source, expected) != tree:
            raise ValueError("Source checkout changed during collection")
        missing = [package["name"] + "@" + package["version"] for package in packages
                   if package["missingExplicitNoticeText"]]
        report = {
            "schema": "cordis-verus.toolchain-source-companion/v1",
            "purpose": "Source and notice preservation for review; not a completed license audit or complete binary SBOM.",
            "verus": {"version": lock["verus"]["version"], "commit": expected, "tree": tree},
            "cargo": command([cargo, "--version"], cwd=source, env=env).strip(),
            "manifest": "verus-source/source/Cargo.toml", "locked": True,
            "cargoLockSha256": sha256(source_dir / "source/Cargo.lock"),
            "z3": {"version": "4.16.0", "licenseUrl": args.z3_license_url,
                   "licenseSha256": args.z3_license_sha256, "licenseFile": str(z3_license.relative_to(stage))},
            "sourceNoticeFiles": notice_files(source_dir, stage),
            "packages": packages, "packagesMissingExplicitNoticeText": missing,
            "boundaries": [
                "Cargo inventory covers source/Cargo.toml and its locked dependencies, including build/dev/platform packages; it is not an assertion that every package is linked into each binary.",
                "All tracked Verus source and full Cargo-vendored package contents are retained, including nested native sources and their packaged notices.",
                "Notice candidates and package license expressions require maintainer review; missing explicit text is reported rather than filled with an inferred license.",
                "Rust rustc-dev/toolchain components, platform system libraries, and dependencies of auxiliary workspaces are not automatically inventoried by this Cargo graph.",
                "Z3 is accompanied by its pinned license text; its full source is not included here.",
            ],
        }
        (stage / "sources-and-notices.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        (stage / "README.md").write_text(
            "# Verus toolchain source and notice companion\n\n"
            "This directory preserves tracked Verus source and complete Cargo-vendored packages, "
            "including the license and notice files shipped inside nested native sources. "
            "The corresponding toolchain ZIP files remain unchanged upstream bytes.\n\n"
            "See `sources-and-notices.json` for pinned inputs, package license metadata, notice "
            "candidates and packages without explicit notice text. These materials support review; "
            "they do not certify license compliance or form a complete binary SBOM.\n\n"
            "`vendor-config.toml` is Cargo's configuration fragment with a relative `vendor` path; "
            "adjust the path for the configuration location before using it. Follow the upstream "
            "Verus build instructions. A full Verus build also needs components outside the Cargo "
            "graph, including rustc-dev and Z3. Rust toolchain and system-library source/licenses "
            "are not automatically covered by this inventory. The Z3 license is included, not its "
            "full source. This archive is not a standalone rebuild guarantee.\n",
            encoding="utf-8")
        if output.exists():
            raise ValueError("--output appeared during collection; refusing to overwrite it")
        stage.rename(output)
    print("Source/notice companion: " + str(output))
    print("Packages: " + str(len(packages)) + "; missing explicit notice text: " + str(len(missing)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True, help="New directory to stage; existing paths are never overwritten")
    parser.add_argument("--cargo", default=os.environ.get("CARGO", "cargo"))
    parser.add_argument("--offline", action="store_true")
    parser.add_argument("--z3-license-url", default=Z3_URL)
    parser.add_argument("--z3-license-sha256", default=Z3_SHA256)
    parser.add_argument("--z3-license-file", type=Path, help="Use cached license bytes, with the same SHA256 check")
    args = parser.parse_args()
    lock = json.loads((ROOT / "toolchain.lock.json").read_text(encoding="utf-8"))
    try:
        collect(args, lock)
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        parser.exit(1, "toolchain-notices: " + str(error) + "\n")


if __name__ == "__main__":
    main()
