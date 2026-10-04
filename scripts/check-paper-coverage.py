#!/usr/bin/env python3
"""Validate the complete numbered paper ledger; never infer proof coverage.

The normal mode checks numbering, evidence symbols, and the generated view. It
does not assert that an item is proved. --require-complete is deliberately a
separate, failing gate while any original claim or integration obligation is
open/refuted. Verus, rather than this inventory check, checks proof bodies.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
LEDGER = ROOT / "docs/paper-obligations.json"
VIEW = ROOT / "docs/paper-coverage.md"
STATUSES = {"formalized", "proved", "partial", "refuted", "missing"}
KINDS = {"Definition", "Theorem", "Lemma", "Corollary"}
ACCEPTED = {"formalized", "proved"}


def validate(data):
    if data.get("schema") != "cordis-verus.paper-obligations/v1":
        raise ValueError("Unrecognized ledger schema")
    items = data["items"]
    if [item["id"] for item in items] != list(range(1, 82)):
        raise ValueError("Exactly the ordered paper items 1 through 81 are required")
    for item in items:
        label = f"{item['kind']} {item['id']}"
        if item["kind"] not in KINDS or item["status"] not in STATUSES:
            raise ValueError(f"Invalid kind/status for {label}")
        if item["status"] == "proved" and item["kind"] == "Definition":
            raise ValueError(f"A definition is formalized, not proved: {label}")
        if item["status"] == "formalized" and item["kind"] != "Definition":
            raise ValueError(f"A claim needs a proof status: {label}")
        if not item["title"] or not item["scope"]:
            raise ValueError(f"Missing title or scope for {label}")
        if item["status"] != "missing" and not item["evidence"]:
            raise ValueError(f"Missing evidence for {label}")
        for evidence in item["evidence"]:
            path = (ROOT / evidence["file"]).resolve()
            if not path.is_relative_to(ROOT) or path.suffix != ".rs":
                raise ValueError(f"Evidence must be a project Rust source: {label}")
            if not path.is_file():
                raise ValueError(f"Missing evidence file: {path}")
            symbol = evidence["symbol"]
            if not re.search(r"\b(?:fn|struct|enum|type)\s+" + re.escape(symbol) + r"\b", path.read_text()):
                raise ValueError(f"Missing evidence symbol {evidence['file']}::{symbol} for {label}")
    if not data.get("integrationObligations"):
        raise ValueError("Whole-project integration obligations must not be omitted")
    ids = [item["id"] for item in data["integrationObligations"]]
    if len(ids) != len(set(ids)):
        raise ValueError("Duplicate integration obligation")
    for item in data["integrationObligations"]:
        if item["status"] not in {"open", "proved"} or not item["description"]:
            raise ValueError("Invalid integration obligation")
    # If the immutable research cache exists, verify exact numbering and kinds.
    source = ROOT / "reference/arxiv-2608.25512v1.txt"
    if source.is_file():
        headings = [(kind, int(number)) for kind, number in re.findall(
            r"^(Definition|Lemma|Theorem|Corollary) (\d+)\.", source.read_text(), re.M)]
        if headings != [(item["kind"], item["id"]) for item in items]:
            raise ValueError("Ledger numbering/kinds differ from the paper snapshot")


def render(data):
    counts = Counter(item["status"] for item in data["items"])
    lines = ["# 论文逐项覆盖清单", "",
             "本表由 `docs/paper-obligations.json` 生成，覆盖 arXiv:2608.25512v1 的全部 81 个编号条目。",
             "状态是对原文陈述的审计结论，不是 Verus 函数数。`proved` 表示对应证明，`formalized` 表示定义已编码；",
             "`partial` 表示仅有受限情形或尚缺连接，`refuted` 表示原文存在已验证反例。证据链接的存在不替代定理前提审查。", "",
             "当前计数：" + "；".join(f"{status} {counts[status]}" for status in sorted(STATUSES)) + "。", "",
             "常规 `quality.sh` 检查清单完整、源码符号存在和本表未过期；只有单独运行",
             "`python3 scripts/check-paper-coverage.py --require-complete` 才检查整篇完成门槛。目前该命令应失败。", "",
             "| 条目 | 状态 | 机械化证据 | 范围或缺口 |",
             "| --- | --- | --- | --- |"]
    for item in data["items"]:
        refs = ", ".join(f"[{e['symbol']}](../{e['file']})" for e in item["evidence"])
        lines.append(f"| {item['kind']} {item['id']} — {item['title']} | {item['status']} | {refs} | {item['scope']} |")
    lines += ["", "## 整体连接义务", ""]
    for item in data["integrationObligations"]:
        lines.append(f"- **{item['id']}** ({item['status']}): {item['description']}")
    lines += ["", "原文辅助引理的反例及尚未闭合的表示义务意味着不能原样宣称整篇已证明。修订版应另行列明改动、",
              "证明适用条件和与实现的对应；不能通过把本表中的反例改标为完成来消除它们。", ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="Regenerate the Markdown inventory")
    parser.add_argument("--require-complete", action="store_true", help="Reject incomplete/refuted original claims and open integration obligations")
    args = parser.parse_args()
    try:
        data = json.loads(LEDGER.read_text())
        validate(data)
        expected = render(data)
        if args.write:
            VIEW.write_text(expected)
        elif not VIEW.is_file() or VIEW.read_text() != expected:
            raise ValueError("Generated paper-coverage.md is stale; use --write")
        incomplete = [f"{i['kind']} {i['id']} ({i['status']})" for i in data["items"] if i["status"] not in ACCEPTED]
        open_integration = [i["id"] for i in data["integrationObligations"] if i["status"] != "proved"]
        print(f"Paper inventory: 81/81 entries; {len(incomplete)} incomplete/refuted; {len(open_integration)} open integration obligations.")
        if args.require_complete and (incomplete or open_integration):
            print("Paper completion gate: FAILED. " + ", ".join(incomplete + open_integration), file=sys.stderr)
            return 1
        print("Inventory consistency passed. This does not certify paper completion.")
        return 0
    except (OSError, KeyError, ValueError) as error:
        print(f"Paper inventory error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
