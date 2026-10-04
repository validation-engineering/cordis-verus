#!/usr/bin/env python3
"""Check pinned research inputs without changing repositories or accessing the network."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent


def local_path(value):
    path = (ROOT / value).resolve()
    if not path.is_relative_to(ROOT):
        raise ValueError(f"Lock path escapes the project: {value}")
    return path


def git(path, *args):
    return subprocess.check_output(
        ["git", "-C", str(path), *args], text=True, stderr=subprocess.PIPE
    ).strip()


def assert_equal(label, actual, expected):
    if actual != expected:
        raise ValueError(f"{label}: expected {expected!r}, got {actual!r}")


def require_clean(path):
    dirty = git(path, "status", "--porcelain=v1", "--untracked-files=all")
    if dirty:
        raise ValueError(f"Dirty upstream worktree {path.relative_to(ROOT)}:\n{dirty}")


def fetch_pinned(repo):
    path = local_path(repo["path"])
    if path.exists() and any(path.iterdir()):
        assert_equal("repository root", Path(git(path, "rev-parse", "--show-toplevel")).resolve(), path)
        require_clean(path)
    else:
        path.mkdir(parents=True, exist_ok=True)
        git(path, "init")
        git(path, "remote", "add", "origin", repo["url"])
    # Fetch the exact immutable object, never the moving branch recorded as context.
    git(path, "fetch", "--depth=1", repo["url"], repo["revision"])
    git(path, "checkout", "--detach", repo["revision"])


def check_repo(name, repo):
    path = local_path(repo["path"])
    if not path.is_dir():
        raise ValueError(f"Missing {repo['path']}; run scripts/check-upstream.py --fetch")
    assert_equal(f"{name} repository root", Path(git(path, "rev-parse", "--show-toplevel")).resolve(), path)
    assert_equal(f"{name} commit", git(path, "rev-parse", "HEAD"), repo["revision"])
    assert_equal(f"{name} tree", git(path, "rev-parse", "HEAD^{tree}"), repo["tree"])
    for relative, expected in repo.get("sourceTrees", {}).items():
        assert_equal(f"{name}:{relative}", git(path, "rev-parse", f"HEAD:{relative}"), expected)
    require_clean(path)
    print(f"OK {name}: {repo['revision']} (clean; source trees match)")


def check_file(relative, expected):
    path = local_path(relative)
    if not path.is_file():
        raise ValueError(f"Missing locked local reference: {relative}")
    hasher = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            hasher.update(chunk)
    assert_equal(relative, hasher.hexdigest(), expected)
    print(f"OK {relative}: SHA256 matches")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--fetch", action="store_true",
        help="Fetch and check out locked Git revisions; refuse to change dirty repositories. Does not download paper files.",
    )
    args = parser.parse_args()
    lock = json.loads((ROOT / "upstream.lock.json").read_text())
    failures = []
    for name, repo in lock["repositories"].items():
        try:
            if args.fetch:
                fetch_pinned(repo)
            check_repo(name, repo)
        except (ValueError, OSError, subprocess.CalledProcessError) as error:
            detail = error.stderr.strip() if isinstance(error, subprocess.CalledProcessError) else str(error)
            failures.append(f"{name}: {detail}")
    paper = lock["paper"]
    for path_key, hash_key in [("path", "sha256"), ("textPath", "textSha256")]:
        try:
            check_file(paper[path_key], paper[hash_key])
        except (ValueError, OSError) as error:
            failures.append(str(error))
    try:
        verus = lock["verusRelease"]
        toolchain = json.loads(local_path(verus["toolchainLock"]).read_text())["verus"]
        for key, locked_key in [("version", "version"), ("tag", "tag"), ("commit", "revision")]:
            assert_equal(f"Verus {key}", toolchain[key], verus[locked_key])
        print("OK Verus release: upstream and toolchain locks agree")
    except (ValueError, OSError, KeyError) as error:
        failures.append(str(error))
    for failure in failures:
        print(f"FAIL {failure}", file=sys.stderr)
    return bool(failures)


if __name__ == "__main__":
    sys.exit(main())
