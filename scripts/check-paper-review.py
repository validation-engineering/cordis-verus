#!/usr/bin/env python3
"""Check five review entry points; no compilation, tests or proof claims."""

import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import sys


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def inside(root, relative):
    path = (root / relative).resolve()
    require(path.is_relative_to(root), f"Path escapes repository: {relative}")
    require(path.is_file(), f"Missing file: {relative}")
    return path


def check(root, index_path, guide_path):
    index = read_json(index_path)
    require(index["schema"] == "cordis-verus.paper-review/v1", "Unknown review schema")
    paper = read_json(root / "upstream.lock.json")["paper"]
    ledger = read_json(root / "docs/paper-obligations.json")
    items = {item["id"]: item for item in ledger["items"]}
    for field, value in index["paper"].items():
        require(value == paper[field], f"Paper lock differs: {field}")
    require(set(index["paper"]) == {"version", "url", "pdfUrl", "sha256", "textSha256"},
            "Incomplete paper identity")
    guide = guide_path.read_text(encoding="utf-8")
    for link in re.findall(r"\]\(([^)]+)\)", guide):
        if "://" in link or link.startswith("#"):
            continue
        relative = Path(index["guide"]).parent / link.split("#", 1)[0]
        # The two new documentation files may be staged outside the repository.
        if relative.as_posix() == index["guide"]:
            continue
        if relative.as_posix() == "docs/paper-review-cases.json":
            continue
        inside(root, relative)

    tree = ast.parse((root / "scripts/check-negative.py").read_text(encoding="utf-8"))
    function = next(node for node in tree.body
                    if isinstance(node, ast.FunctionDef) and node.name == "mutation_manifest")
    returns = [node for node in function.body if isinstance(node, ast.Return)]
    require(len(returns) == 1, "Unexpected mutation_manifest shape")
    mutations = {item[0] for item in ast.literal_eval(returns[0].value)}

    text_path = root / paper["textPath"]
    paper_text = None
    if text_path.exists():
        content = text_path.read_bytes()
        require(hashlib.sha256(content).hexdigest() == paper["textSha256"],
                "Local paper text differs from lock")
        paper_text = content.decode("utf-8")

    seen = set()
    tests = 0
    symbols = 0
    for case in index["cases"]:
        case_id = case["id"]
        require(case_id not in seen, f"Duplicate case: {case_id}")
        seen.add(case_id)
        require(f"## {case_id}:" in guide, f"Missing guide heading: {case_id}")
        require(case["classification"] and case["paper"]["clauses"], f"Missing scope: {case_id}")
        for entry in case["paper"]["items"]:
            item = items[entry["id"]]
            require(entry["status"] == item["status"], f"Ledger status differs: {case_id}, {item['id']}")
            if paper_text is not None:
                # Match a numbered statement heading, not an earlier reference.
                statement = re.search(rf"^{re.escape(item['kind'])}\s+{item['id']}\.",
                                      paper_text, re.MULTILINE)
                require(statement is not None, f"Paper heading absent: {item['id']}")
                prefix = paper_text[:statement.start()]
                pages = re.findall(r"=== PDF page (\d+) ===", prefix)
                sections = re.findall(r"^(\d+(?:\.\d+)+)\.\s+[^\n]+", prefix, re.MULTILINE)
                require(pages and int(pages[-1]) in case["paper"]["pages"],
                        f"Paper page differs: {case_id}, {item['id']}")
                require(sections and sections[-1] == case["paper"]["section"],
                        f"Paper section differs: {case_id}, {item['id']}")
        for symbol in case["symbols"]:
            source = inside(root, symbol["file"]).read_text(encoding="utf-8")
            require(symbol["kind"] in {"fn", "struct"}, f"Unsupported symbol kind: {case_id}")
            declaration = rf"\b{symbol['kind']}\s+{re.escape(symbol['symbol'])}\b"
            require(re.search(declaration, source),
                    f"Source symbol absent: {symbol['file']}::{symbol['symbol']}")
            symbols += 1
        for test in case["tests"]:
            crate = f"crates/{test['package']}"
            manifest = inside(root, f"{crate}/Cargo.toml").read_text(encoding="utf-8")
            require(re.search(rf'^name\s*=\s*"{re.escape(test["package"])}"\s*$', manifest, re.MULTILINE),
                    f"Cargo package differs: {crate}")
            source = inside(root, f"{crate}/tests/{test['target']}.rs").read_text(encoding="utf-8")
            require(re.search(rf"#\[test\]\s*fn\s+{re.escape(test['name'])}\s*\(", source),
                    f"Regression absent: {test['target']}::{test['name']}")
            command = (f"cargo test --offline -p {test['package']} --test "
                       f"{test['target']} {test['name']} -- --exact")
            require(command in guide, f"Guide command absent: {command}")
            tests += 1
        negative = case["negativeControl"]
        require(negative["name"] in mutations, f"Unknown mutation candidate: {case_id}")
        require(negative["name"] in guide, f"Guide mutation absent: {case_id}")
        require(negative["evidence"] == "candidate-only; inspect source-bound acceptance separately",
                f"Index is not an acceptance report: {case_id}")
    require(seen == {f"PR-{n:02d}" for n in range(1, 6)}, "Expected the five initial review cases")
    text_result = "locked local text checked" if paper_text is not None else "local text absent; lock checked"
    print(f"Paper review index consistent: {len(seen)} cases, {symbols} symbol references, "
          f"{tests} named regressions; {text_result}.")
    print("No tests or verification were run; semantic correspondence still requires review.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--index", type=Path)
    parser.add_argument("--guide", type=Path)
    args = parser.parse_args()
    root = args.root.resolve()
    try:
        check(root, args.index or root / "docs/paper-review-cases.json",
              args.guide or root / "docs/paper-review-guide.md")
    except (ValueError, KeyError, StopIteration, OSError, TypeError) as error:
        print(f"Paper review check failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
