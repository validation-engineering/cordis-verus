#!/usr/bin/env python3
"""Build and test extracted crate archives without uploading or using source paths.

The local crates are unpublished, so command-local Cargo patches resolve each
dependent to already extracted artifacts in dependency order. This checks package
contents, not registry name availability or crates.io publish eligibility.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parent.parent
PACKAGE_ORDER = ("cordis-kernel", "cordis-driver", "cordis")


def cargo_patches(paths):
    """Build command-local patches without writing repository Cargo configuration."""
    return [argument for name, path in paths.items()
            for argument in ("--config", "patch.crates-io." + name + ".path=" + json.dumps(str(path)))]


def run(args, cwd=ROOT, capture=False):
    print("+ " + " ".join(str(arg) for arg in args), flush=True)
    result = subprocess.run(
        [str(arg) for arg in args], cwd=cwd, check=True, text=True,
        stdout=subprocess.PIPE if capture else None,
    )
    return result.stdout if capture else None


def extract(archive, destination, prefix):
    with tarfile.open(archive, "r:gz") as bundle:
        entries = bundle.getmembers()
        names = set()
        for entry in entries:
            name = PurePosixPath(entry.name)
            if name.is_absolute() or ".." in name.parts or name.parts[0] != prefix:
                raise RuntimeError(f"Unsafe archive path: {entry.name}")
            if not (entry.isfile() or entry.isdir()):
                raise RuntimeError(f"Unsupported archive entry: {entry.name}")
            if entry.name in names:
                raise RuntimeError(f"Duplicate archive path: {entry.name}")
            names.add(entry.name)
            relative = "/".join(name.parts[1:])
            if any(part in {".tools", ".git", "upstream", "reference", "target"} for part in name.parts):
                raise RuntimeError(f"Local cache leaked into artifact: {entry.name}")
            if relative.endswith((".pdf", ".rlib", ".vir")):
                raise RuntimeError(f"Unexpected generated/research artifact: {entry.name}")
        for required in ("Cargo.toml", "Cargo.lock", "README.md", "LICENSE", "NOTICE", "src/lib.rs"):
            if f"{prefix}/{required}" not in names:
                raise RuntimeError(f"Missing required package file: {required}")
        for entry in entries:
            path = destination / entry.name
            if entry.isdir():
                path.mkdir(parents=True, exist_ok=True)
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                with bundle.extractfile(entry) as stream:
                    path.write_bytes(stream.read())
        return sorted(names)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--offline", action="store_true", help="Use only cached registry dependencies")
    args = parser.parse_args()
    os.environ["PATH"] = str(Path(os.environ.get("CARGO_HOME", Path.home() / ".cargo")) / "bin") + os.pathsep + os.environ.get("PATH", "")
    lock = json.loads((ROOT / "toolchain.lock.json").read_text())
    os.environ["RUSTUP_TOOLCHAIN"] = lock["rust"]["channel"]
    network = ["--offline"] if args.offline else []
    metadata = json.loads(run(["cargo", "metadata", "--no-deps", "--format-version", "1", "--locked", *network], capture=True))
    packages = {package["name"]: package for package in metadata["packages"]}
    output = ROOT / "target" / "release-artifacts"
    output.mkdir(parents=True, exist_ok=True)
    report_path = output / "package-report.json"
    # A failed new run must not leave an older success report looking current.
    if report_path.exists():
        report_path.unlink()
    report = {
        "schema_version": 1,
        "rust": lock["rust"]["channel"],
        "registry_publish_checked": False,
        "inputs": {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in ("Cargo.lock", "toolchain.lock.json")},
        "packages": [],
        "excluded": [{"name": "cordis-node", "reason": "Native binding is not a public Rust crate; validate its packed Node distribution with scripts/check-npm-package.mjs."}],
    }
    with tempfile.TemporaryDirectory(prefix="cordis-artifacts-") as temporary:
        extracted = Path(temporary).resolve()
        extracted_paths = {}
        assembly_paths = {}
        for name in PACKAGE_ORDER:
            package = packages[name]
            version = package["version"]
            for required in ("description", "license", "readme", "rust_version"):
                if not package.get(required):
                    raise RuntimeError(f"{name}: missing metadata {required}")
            for filename in ("LICENSE", "NOTICE"):
                if (Path(package["manifest_path"]).parent / filename).read_bytes() != (ROOT / filename).read_bytes():
                    raise RuntimeError(f"{name}: {filename} differs from project notice")
            local_patch = cargo_patches(extracted_paths)
            # Assembly and verification are separate: --no-verify is NOT a pass.
            run(["cargo", "package", "-p", name, "--allow-dirty", "--locked", "--no-verify", *network, *cargo_patches(assembly_paths)])
            archive_name = f"{name}-{version}.crate"
            archive = ROOT / "target" / "package" / archive_name
            prefix = f"{name}-{version}"
            files = extract(archive, extracted, prefix)
            artifact_root = extracted / prefix
            isolated_metadata = json.loads(run(["cargo", "metadata", "--format-version", "1", "--locked", *network, *local_patch], cwd=artifact_root, capture=True))
            for dependency in isolated_metadata["packages"]:
                if dependency["source"] is None and not Path(dependency["manifest_path"]).resolve().is_relative_to(extracted):
                    raise RuntimeError(f"Build escaped extracted artifacts: {dependency['manifest_path']}")
            shared_target = ["--target-dir", str(ROOT / "target" / "package-check")]
            run(["cargo", "test", "--all-targets", "--locked", *network, *local_patch, *shared_target], cwd=artifact_root)
            run(["cargo", "test", "--doc", "--locked", *network, *local_patch, *shared_target], cwd=artifact_root)
            run(["cargo", "build", "--release", "--lib", "--locked", *network, *local_patch, *shared_target], cwd=artifact_root)
            shutil.copyfile(archive, output / archive_name)
            extracted_paths[name] = artifact_root
            assembly_paths[name] = Path(package["manifest_path"]).parent
            report["packages"].append({"name": name, "version": version, "sha256": hashlib.sha256(archive.read_bytes()).hexdigest(), "files": files, "tests": "passed", "doctests": "passed", "release_build": "passed"})
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{len(report['packages'])} extracted artifacts tested and release-built. Report: {report_path}")
    print("No package was uploaded. Registry namespace and publish eligibility remain release-time checks.")


if __name__ == "__main__":
    main()
