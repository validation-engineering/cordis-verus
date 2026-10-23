#!/usr/bin/env python3
"""Validate/render the paper-to-code inventory, never certify theorem completion."""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
INVENTORY = Path("docs/paper-mapping-inventory.json")
LEDGER = Path("docs/paper-obligations.json")
PLAN = Path("docs/paper-refinement-plan.json")
VIEWS = {"en": Path("docs/paper-mapping-inventory.md"),
         "zh-CN": Path("docs/paper-mapping-inventory.zh-CN.md")}
BASELINE_IDS = tuple(
    [f"S{i:02}" for i in range(1, 8)] + [f"P{i:02}" for i in range(1, 6)]
    + [f"R{i:02}" for i in range(1, 10)] + [f"G{i:02}" for i in range(1, 8)]
    + ["C01", "D01", "D02"])
INTEGRATIONS = {"whole-lifecycle", "corrected-specification",
                "executable-simulation", "host-boundary"}
SURFACES = {"semantics", "native", "mixed", "fresh", "async", "node",
            "configuration", "host"}
KINDS = {"specification", "code_contract", "undischarged", "environment", "acceptance"}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def bilingual(value, label):
    require(isinstance(value, dict) and set(value) == {"en", "zh-CN"}
            and all(isinstance(x, str) and x.strip() for x in value.values()),
            f"Missing bilingual text: {label}")


def file_path(name, root):
    require(isinstance(name, str), "Invalid input path")
    relative = Path(name)
    path = (root / relative).resolve()
    require(not relative.is_absolute() and ".." not in relative.parts
            and path.is_relative_to(root.resolve()) and path.is_file(),
            f"Missing or unsafe input path: {name}")
    return path


def unique(values, allowed, label):
    require(isinstance(values, list) and values
            and all(isinstance(x, str) for x in values)
            and len(values) == len(set(values)) and set(values) <= set(allowed),
            f"Invalid/duplicate {label}")


def review(refs, root, label):
    require(isinstance(refs, list) and refs, f"Missing review path: {label}")
    for ref in refs:
        path = file_path(ref["file"], root)
        symbol = ref["symbol"]
        require(path.suffix == ".rs" and isinstance(symbol, str)
                and re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", symbol),
                f"Invalid review symbol: {label}")
        require(re.search(r"\b(?:fn|struct|enum|type)\s+" + re.escape(symbol) + r"\b",
                          path.read_text()), f"Missing review symbol: {ref['file']}::{symbol}")


def validate(data, ledger, plan, root=ROOT, check_inputs=True):
    require(data.get("schema") == "cordis-verus.paper-mapping-inventory/v1", "Unknown inventory schema")
    require(data.get("baseline") == "2026-10-20.v1", "Review baseline/version migration explicitly")
    require(data.get("paper") == ledger["paper"] == plan["paper"]
            and data.get("ledger") == str(LEDGER) and data.get("plan") == str(PLAN),
            "Inventory must use the original paper and existing plan")
    require([x["id"] for x in ledger["items"]] == list(range(1, 82)), "Original ledger is incomplete")
    for item in ledger["items"]:
        review(item["evidence"], root, f"original item {item['id']}")
    require({x["id"] for x in ledger["integrationObligations"]} == INTEGRATIONS,
            "Original integration obligations changed")
    require(data.get("completionClaims") == {
        "originalPaperProved": False, "implementationMappingComplete": False,
        "milestonesReclassified": False, "newVerificationRun": False},
        "An inventory must not claim a new proof or milestone completion")
    for field in ("purpose", "dependencyMeaning", "closureRule", "estimation", "changePolicy"):
        bilingual(data.get(field), field)
    require([t["id"] for t in data["targets"]] == ["original-audit", "implementation-mapping"],
            "Keep original audit and implementation mapping separate")
    for target in data["targets"]:
        bilingual(target["description"], target["id"])
    require([(x["id"], x["profile"]) for x in data["retainedBaselines"]] ==
            [("R1", "finite-strict-context/v1"), ("R2", "managed-production/v1")],
            "Retain scoped R1/R2 baselines")
    milestones = {m["id"]: m for m in plan["milestones"]}
    require(all(milestones[mid]["status"] == "complete" for mid in ("R1", "R2"))
            and plan["r1Interpretation"]["profile"] == "finite-strict-context/v1"
            and plan["r2Acceptance"]["profile"] == "managed-production/v1",
            "Scoped baseline claims must match the existing plan")
    for baseline in data["retainedBaselines"]:
        file_path(baseline["source"], root)
        bilingual(baseline["note"], baseline["id"])
    require(data.get("changes") and data["changes"][-1]["baseline"] == data["baseline"],
            "Missing baseline change rationale")
    for change in data["changes"]:
        bilingual(change["reason"], "change rationale")

    premises = data["premises"]
    pids = [p["id"] for p in premises]
    require(pids == [f"M{i:02}" for i in range(1, 16)], "All baseline premise sources must remain")
    premise_files = set()
    for premise in premises:
        bilingual(premise["title"], premise["id"])
        bilingual(premise["source"], premise["id"])
        require(premise["kind"] in KINDS, "Unknown premise source kind")
        review(premise["review"], root, premise["id"])
        premise_files.update(r["file"] for r in premise["review"])
    require({p["id"] for p in premises if p["kind"] == "environment"} == {"M09", "M10"},
            "Core semantic/target/ownership obligations cannot become environment assumptions")

    tasks = data["obligations"]
    ids = [t["id"] for t in tasks]
    require(tuple(ids) == BASELINE_IDS, "Retain all 31 baseline IDs; additions/splits need an explicit baseline migration")
    graph, task_files = {}, set()
    for task in tasks:
        tid = task["id"]
        for field in ("title", "current", "remaining", "validation"):
            bilingual(task[field], f"{tid}/{field}")
        require(task["category"] in {"semantics", "audit", "production", "boundary",
                                    "recovery", "global", "configuration", "delivery"}, "Unknown category")
        require(task["stage"] in {"specification", "composition", "integration", "acceptance"}, "Unknown stage")
        require(task["risk"] in {"high", "medium", "low"}, "Unknown risk")
        require(task["status"] in {"open", "closed"}, "Unknown closure status")
        numbers = task["paperItems"]
        require(isinstance(numbers, list) and numbers and all(type(n) is int and 1 <= n <= 81 for n in numbers)
                and len(numbers) == len(set(numbers)), f"Invalid paper items: {tid}")
        deps = task["dependsOn"]
        require(isinstance(deps, list) and all(isinstance(x, str) for x in deps)
                and len(deps) == len(set(deps)) and set(deps) <= set(ids), f"Invalid dependencies: {tid}")
        graph[tid] = deps
        unique(task["premises"], pids, f"{tid} premise sources")
        unique(task["paths"], SURFACES, f"{tid} execution paths")
        require(isinstance(task["closeWhen"], list) and len(task["closeWhen"]) >= 2,
                f"Missing distinct closure criteria: {tid}")
        for criterion in task["closeWhen"]:
            bilingual(criterion, f"{tid} closure")
        review(task["review"], root, tid)
        task_files.update(r["file"] for r in task["review"])
        evidence = task["closureEvidence"]
        require(isinstance(evidence, list), f"Invalid closure evidence: {tid}")
        if task["status"] == "closed":
            require(evidence and all(x["kind"] in {"proof", "caller-review", "reproduction"} for x in evidence)
                    and {x["kind"] for x in evidence} == {"proof", "caller-review", "reproduction"},
                    f"Closure requires proof, caller review and reproduction evidence: {tid}")
            for entry in evidence:
                path = file_path(entry["file"], root)
                require(entry.get("sha256") == hashlib.sha256(path.read_bytes()).hexdigest(),
                        f"Stale closure evidence: {tid}")
                require(entry.get("reviewInputSha256") == data["reviewInputSha256"],
                        f"Closure evidence is not bound to the current review inputs: {tid}")
            require(all(t["status"] == "closed" for t in tasks if t["id"] in deps),
                    f"Closure prerequisites remain open: {tid}")
        else:
            require(not evidence, f"Partial historical evidence belongs in review, not closureEvidence: {tid}")

    seen, active = set(), set()
    def visit(tid):
        require(tid not in active, f"Cyclic closure dependency: {tid}")
        if tid in seen:
            return
        active.add(tid)
        for dep in graph[tid]:
            visit(dep)
        active.remove(tid)
        seen.add(tid)
    for tid in ids:
        visit(tid)

    rows = data["items"]
    require([r["paperItem"] for r in rows] == list(range(1, 82)),
            "Every numbered paper entry must appear exactly once")
    for row in rows:
        n = row["paperItem"]
        bilingual(row["implementationNote"], f"paper item {n}")
        expected = [t["id"] for t in tasks if n in t["paperItems"]]
        require(row["obligations"] == expected and any(not x.startswith("D") for x in expected),
                f"Paper item {n} needs exact substantive obligations, not only final acceptance")
    integration = data["integration"]
    require(len(integration) == 4 and {i["id"] for i in integration} == INTEGRATIONS,
            "All four integration obligations must remain")
    for item in integration:
        unique(item["obligations"], ids, item["id"])
        bilingual(item["closeWhen"], item["id"])
        require(any(not i.startswith("D") for i in item["obligations"]), "Integration needs substantive obligations")
    surfaces = data["surfaces"]
    require(len(surfaces) == 8 and {s["id"] for s in surfaces} == SURFACES,
            "Include unnumbered extensions and all eight execution surfaces")
    for surface in surfaces:
        bilingual(surface["title"], surface["id"])
        require(surface["paperLocation"] and surface["obligations"] ==
                [t["id"] for t in tasks if surface["id"] in t["paths"]],
                f"Execution surface coverage mismatch: {surface['id']}")
    expected_r3 = {
        "R3-A": ["R01", "R02"], "R3-B": ["R03", "R04"], "R3-C": ["R05", "R06", "R07"],
        "R3-D": ["R08", "R09", "D01", "D02"],
    }
    require(len(data["r3Packages"]) == 4 and
            {x["id"]: x["obligations"] for x in data["r3Packages"]} == expected_r3,
            "Retain all fixed R3-A/B/C/D acceptance obligations")
    unique(data["priorityRisks"], ids, "priority risks")
    require(all(t["risk"] == "high" for t in tasks if t["id"] in data["priorityRisks"]),
            "Priority risk lacks high-risk classification")

    bindings = data["reviewInputSha256"]
    required = {str(LEDGER), str(PLAN), "toolchain.lock.json", "upstream.lock.json",
                "docs/r1-semantics.md", "docs/r2-acceptance.md", "docs/r3-remaining-work.md",
                "docs/r3-controlled-effects.md"} | premise_files | task_files
    required.update(r["file"] for item in ledger["items"] for r in item["evidence"])
    require(set(bindings) == required, "Review fingerprint must cover exactly the declared review inputs")
    for name, sha in bindings.items():
        path = file_path(name, root)
        require(isinstance(sha, str) and re.fullmatch(r"[0-9a-f]{64}", sha), f"Invalid input fingerprint: {name}")
        if check_inputs:
            require(hashlib.sha256(path.read_bytes()).hexdigest() == sha,
                    f"Review input changed: {name}; re-audit affected obligations, do not relabel old proof evidence")


def render(data, ledger, plan, lang):
    zh = lang == "zh-CN"
    def tr(en, cn):
        return cn if zh else en
    def t(value):
        return value[lang]
    def links(ids):
        return ", ".join(f"[{i}](#{i.lower()})" for i in ids)
    def source_refs(refs):
        return "; ".join(f"[{Path(r['file']).name}::{r['symbol']}](../{r['file']})" for r in refs)
    def esc(value):
        return value.replace("|", "\\|").replace("\n", " ")
    counts = Counter(x["status"] for x in ledger["items"])
    tasks = data["obligations"]
    open_tasks = [x for x in tasks if x["status"] == "open"]
    stages = Counter(x["stage"] for x in open_tasks)
    lines = [
        tr("# Paper-to-code remaining-obligation inventory", "# 论文到代码剩余义务盘点"),
        "",
        tr("[中文](paper-mapping-inventory.zh-CN.md)", "[English](paper-mapping-inventory.md)")
        + " · [JSON](paper-mapping-inventory.json) · "
        + tr("[Original ledger](paper-coverage.md) · [Milestones](paper-refinement-roadmap.md)",
             "[原文台账](paper-coverage.md) · [里程碑](paper-refinement-roadmap.zh-CN.md)"),
        "",
        tr("Generated from the inventory JSON and the existing ledger/plan. Edit the JSON, then run the checker; do not promote paper statuses in this view.",
           "由盘点 JSON 及既有台账／计划生成。编辑 JSON 后运行检查器；不得在本视图提升论文状态。"),
        "",
        f"**{tr('Baseline', '基线')} `{data['baseline']}`** — " + t(data["purpose"]),
        "",
        tr("This is a complete allocation of the reviewed scope, not a promise that no further research issue can arise. R1–R4 remain technical classifications; stable obligation IDs measure closure. R1/R2's scoped completion is retained.",
           "这是对已审查范围的完整分配，不保证研究中不会发现新问题。R1–R4 保留为技术分类；使用稳定义务编号跟踪关闭。R1／R2 的范围内完成状态保留。"),
        "",
        tr("## Current position", "## 当前距离"),
        "",
        tr(f"- Original audit: {counts['formalized']} formalized definitions, {counts['proved']} proved claims, {counts['partial']} partial entries, {counts['refuted']} refuted claims; {sum(i['status'] == 'open' for i in ledger['integrationObligations'])} integration obligations remain open.",
           f"- 原文审计：{counts['formalized']} 项定义已编码、{counts['proved']} 项命题已证明、{counts['partial']} 项部分完成、{counts['refuted']} 项已有反例；{sum(i['status'] == 'open' for i in ledger['integrationObligations'])} 项整体连接义务仍开放。"),
        tr(f"- This remaining-work baseline has **{len(tasks)} closure units**, **{len(open_tasks)} still open**. Their existing proofs and runtime paths are recorded below. This is not a zero-percent project: the list intentionally excludes already closed local work.",
           f"- 本次剩余清单共 **{len(tasks)} 个关闭单元，{len(open_tasks)} 个仍开放**。各项已有证明和运行路径记录在下方。这不表示项目完成度为零：清单刻意只列尚未关闭的最终义务。"),
        tr(f"- The {counts['partial']} partial original entries are: ", f"- 原文 {counts['partial']} 项 partial 编号：")
        + ", ".join(str(i["id"]) for i in ledger["items"] if i["status"] == "partial") + ".",
        tr("- Refuted original entries: ", "- 原文 refuted 编号：")
        + ", ".join(str(i["id"]) for i in ledger["items"] if i["status"] == "refuted") + ". "
        + tr("Corrected-contract acceptance cannot make the original-proof gate pass.",
             "修订合同验收不能让原文证明门槛通过。"),
        tr("- Remaining stages: ", "- 剩余阶段：")
        + ", ".join(f"{k} {v}" for k, v in sorted(stages.items())) + ".",
        "",
        tr("Stages describe the main remaining work: specification = settle a precise statement; composition = derive the combined theorem from actual sources; integration = connect/enforce the production path; acceptance = review and reproduce the completed chain. They are not percentages.",
           "阶段表示主要剩余工作：specification＝确定精确陈述；composition＝从实际来源推导组合定理；integration＝接通并约束生产路径；acceptance＝审查和复现完成后的证明链。阶段不是百分比。"),
        "",
        t(data["estimation"]),
        "",
        tr("The old development report belongs to its recorded tree. This inventory adds no Verus run and does not refresh that report. Review-input hashes below detect changed audit inputs; they are not proof evidence. Release/platform installation is tracked separately from semantic completion.",
           "原开发报告属于其记录的源码树。本盘点没有新增 Verus 验证，也不刷新该报告。下方审查输入哈希用于检测审计材料变化，不是证明证据。发布／平台安装与语义完成分开跟踪。"),
        "",
        tr("## Completion targets and preserved work", "## 完成目标与保留成果"),
        "",
    ]
    for target in data["targets"]:
        lines += [f"- **`{target['id']}`**: {t(target['description'])}"]
    lines += ["", t(data["closureRule"]), ""]
    for baseline in data["retainedBaselines"]:
        base_path = Path(baseline["source"])
        base_link = base_path.stem + ".zh-CN.md" if zh else base_path.name
        lines += [f"- **{baseline['id']} / `{baseline['profile']}`**: {t(baseline['note'])} "
                  f"[{tr('Scope','范围')}]({base_link})"]
    lines += ["", tr("## Closure order and highest uncertainty", "## 关闭顺序与最大不确定性"), "",
              t(data["dependencyMeaning"]), "",
              tr("Resolve or sharply bound these risks first: ", "优先消除或明确限定这些风险：") + links(data["priorityRisks"]) + ".", "",
              tr("The first implementation sequence is the context/domain audit and controlled-access boundary (S01/S02/P01), then actual target-state correspondence (R01). In parallel, check the source-frozen-map versus target-reexecution bridge (R08) and independence (G02) early; do not wait for the full scheduler to discover a semantic mismatch. General progress and confluence (G04/G07) remain separate high-risk conclusions, not presumed consequences of local tests.",
                 "首要实施顺序是上下文／定义域审计及受控访问边界（S01／S02／P01），随后是实际目标状态对应（R01）。同时尽早核对源固定映射与目标重新执行的连接（R08）及独立性（G02），避免完整调度器写完后才暴露语义不匹配。一般进展与合流（G04／G07）仍是独立高风险结论，不能从局部测试预设成立。"),
              "", "```mermaid", "flowchart TD",
              '  S["S01–S03: context, domains, observations"] --> P["P01–P04: controlled production contracts"]',
              '  P --> R["R01–R07: target execution and source closure"]',
              '  P --> I["G02: independence"]',
              '  R --> E["R08: exact recovery equation"]',
              '  I --> E',
              '  R --> D["R09 / G06: legal deletion and normalization"]',
              '  I --> D',
              '  A["S04–S07: original refutations"] --> D',
              '  A --> G["G03–G05: bounds, progress, support"]',
              '  E --> G',
              '  G --> C["G07: applicable confluence"]',
              '  D --> C',
              '  C --> F["C01: configuration convergence"]',
              '  F --> V["D01–D02: final audit and reproduction"]',
              '  B["P05 / R07: host and Node boundaries"] --> V',
              "```", "",
              tr("This diagram is a summary; the exact acyclic closure dependencies are in each unit and JSON.",
                 "图仅概括关系；精确无环关闭依赖在各单元及 JSON 中。"),
              "", tr("## Stable remaining units", "## 固定剩余单元"), "",
              tr("S/P/R/G/C/D are inventory unit prefixes. For example, R01 is a recovery obligation, not the existing R1 milestone. The category totals are 7 semantics/audit, 5 production/boundary, 9 recovery, 7 global, 1 configuration and 2 final-audit/reproduction units.",
                 "S／P／R／G／C／D 是盘点单元前缀。例如 R01 是恢复义务，不是既有里程碑 R1。分类合计为语义／审计 7 项、生产／边界 5 项、恢复 9 项、全局性质 7 项、配置 1 项、最终审查／复现 2 项。"),
              "",
              tr("| ID | Obligation | Current stage / risk | Closure prerequisites |",
                 "| 编号 | 义务 | 当前阶段／风险 | 关闭依赖 |"),
              "| --- | --- | --- | --- |"]
    for task in tasks:
        lines += [f"| [{task['id']}](#{task['id'].lower()}) | {esc(t(task['title']))} | {task['stage']} / {task['risk']} | {links(task['dependsOn']) or '—'} |"]
    lines += ["", tr("## Execution surfaces, including unnumbered claims", "## 执行范围与无编号陈述"), "",
              tr("Numbered-item coverage alone misses §4.4 asynchronous/failure/isolation/configuration arguments and §5 reconciliation/HMR claims. These surfaces are required by this inventory; opaque internals remain explicitly audited obligations, not implicit proof coverage.",
                 "只覆盖编号条目会遗漏 §4.4 异步／失败／隔离／配置推理及 §5 协调／HMR 陈述。本盘点要求覆盖下列范围；不透明内部保留为明确审计义务，不隐含为已证明。"),
              "", tr("| Surface | Paper location | Obligations |", "| 范围 | 论文位置 | 义务 |"), "| --- | --- | --- |"]
    for surface in data["surfaces"]:
        lines += [f"| {t(surface['title'])} | {esc(surface['paperLocation'])} | {links(surface['obligations'])} |"]
    lines += ["", tr("## Every numbered paper item", "## 全部编号论文条目"), "",
              tr("Original statuses and source symbols are read from the original ledger. The first evidence link is an audit entry point; it does not claim that the entire entry is discharged by that symbol. Each row has substantive remaining units in addition to D01/D02.",
                 "原文状态及源码符号读取自原台账。首个证据链接是审计入口，不表示一个符号已经履行整个条目。每行除 D01／D02 外均有实质剩余义务。"),
              "", tr("| # / original statement | Original audit | Implementation connection still to close | Units |",
                     "| 编号／原陈述 | 原文审计 | 仍待闭合的实现连接 | 单元 |"),
              "| --- | --- | --- | --- |"]
    for row, item in zip(data["items"], ledger["items"]):
        refs = item["evidence"][:1]
        # D01/D02 apply to all entries; omit repeated links, retaining them in JSON.
        units = [i for i in row["obligations"] if not i.startswith("D")]
        name = f"{item['kind']} {item['id']}: {item['title']}"
        lines += [f"| {esc(name)} | `{item['status']}` | {esc(t(row['implementationNote']))} {source_refs(refs)} | {links(units)} |"]
    lines += ["", tr("## Four whole-project integration obligations", "## 四项整体连接义务"), "",
              tr("These stay open in the original ledger. Completing a scoped R1/R2 milestone does not automatically close them.",
                 "这些在原台账保持 open；范围内 R1／R2 完成不会自动关闭它们。"),
              "", tr("| Obligation | Closure condition | Units |", "| 义务 | 关闭条件 | 单元 |"), "| --- | --- | --- |"]
    original_integration = {i["id"]: i for i in ledger["integrationObligations"]}
    for item in data["integration"]:
        status = original_integration[item["id"]]["status"]
        lines += [f"| `{item['id']}` ({status}) | {esc(t(item['closeWhen']))} | {links(item['obligations'])} |"]
    lines += ["", tr("## Existing R3 acceptance packages", "## 与既有 R3 验收包的关系"), "",
              tr("The fixed R3-A/B/C/D exits remain unchanged. Additional semantic, production and independence prerequisites are visible in the dependency graph.",
                 "固定 R3-A／B／C／D 退出条件不变；语义、生产及独立性前提在依赖图中明确展示。"), ""]
    for package in data["r3Packages"]:
        lines += [f"- **{package['id']}**: {links(package['obligations'])}"]
    lines += ["", tr("## Premise sources", "## 前提来源"), "",
              tr("`code_contract` means an existing bounded contract, not that every final caller already establishes it. `undischarged` remains a proof obligation. Environment sources do not absorb missing internal semantic proofs.",
                 "`code_contract` 表示已有范围明确的合同，不表示每个最终调用者都已建立它；`undischarged` 仍是证明义务。环境来源不能吸收缺失的内部语义证明。"),
              "", tr("| ID | Premise / source | Kind | Review |", "| 编号 | 前提／来源 | 类型 | 审查 |"), "| --- | --- | --- | --- |"]
    for premise in data["premises"]:
        lines += [f"| <a id=\"{premise['id'].lower()}\"></a>{premise['id']} | **{t(premise['title'])}** — {esc(t(premise['source']))} | `{premise['kind']}` | {source_refs(premise['review'])} |"]
    lines += ["", tr("## Per-unit closure contracts", "## 逐项关闭合同"), ""]
    for task in tasks:
        lines += [f"<a id=\"{task['id'].lower()}\"></a>", "",
                  f"### {task['id']} · {t(task['title'])}", "",
                  f"**{tr('State','状态')}:** `{task['status']}` · `{task['stage']}` · "
                  f"**{tr('Risk','风险')}:** `{task['risk']}`", "",
                  f"**{tr('Already available','已有成果')}:** {t(task['current'])}", "",
                  f"**{tr('Remaining conclusion','剩余结论')}:** {t(task['remaining'])}", "",
                  f"**{tr('Closes only when','关闭条件')}:**", ""]
        lines += [f"{i}. {t(criterion)}" for i, criterion in enumerate(task["closeWhen"], 1)]
        lines += ["", f"**{tr('Validation required','所需验收')}:** {t(task['validation'])}", "",
                  f"**{tr('Premise sources','前提来源')}:** {links(task['premises'])}. "
                  f"**{tr('Closure dependencies','关闭依赖')}:** {links(task['dependsOn']) or '—'}.", "",
                  f"**{tr('Existing review path','现有审查路径')}:** {source_refs(task['review'])}", ""]
    lines += [tr("## Updating and checking this baseline", "## 更新与检查基线"), "",
              t(data["changePolicy"]), "",
              "```sh", "python3 -B scripts/check-paper-mapping.py",
              "python3 -B scripts/check-paper-mapping.py --write",
              "python3 -B -m unittest discover -s scripts/tests -p 'test_check_paper_mapping.py'",
              "```", "",
              tr("The default checker verifies 81/81 rows, all four integrations, all required surfaces, exact bidirectional allocation, acyclic dependencies, actual review symbols, bilingual views and review-input hashes. `--write` regenerates views only; it never refreshes hashes or proof records. When an input changes, review the affected obligations and explicitly update their input bindings after review.",
                 "默认检查器核对 81／81 行、四项整体义务、全部必需范围、精确双向分配、无环依赖、实际审查符号、中英文视图及审查输入哈希。`--write` 只生成视图，不刷新哈希或证明记录。输入变化后须审查受影响义务，并在审查后明确更新输入绑定。"),
              "",
              tr("A passing check establishes inventory consistency and freshness of the declared review inputs only. It proves no Rust contract and cannot replace the unchanged original completion gate:",
                 "检查通过只建立清单一致性及声明审查输入的新鲜性，不证明任何 Rust 合同，也不替代未改变的原文完成门槛："),
              "", "```sh", "python3 -B scripts/check-paper-coverage.py --require-complete", "```", "",
              tr("That original gate still fails while partial/refuted original claims or open integration obligations remain.",
                 "只要仍有 partial／refuted 原文条目或 open 整体义务，该原文门槛就仍会失败。"), ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="Regenerate EN/ZH views; never refresh review hashes or proofs")
    args = parser.parse_args()
    try:
        data = json.loads((ROOT / INVENTORY).read_text())
        ledger = json.loads((ROOT / LEDGER).read_text())
        plan = json.loads((ROOT / PLAN).read_text())
        validate(data, ledger, plan)
        for lang, path in VIEWS.items():
            expected = render(data, ledger, plan, lang)
            if args.write:
                (ROOT / path).write_text(expected)
            else:
                require((ROOT / path).is_file() and (ROOT / path).read_text() == expected,
                        f"Generated inventory view is stale: {path}; use --write after review")
        count = sum(t["status"] == "open" for t in data["obligations"])
        print(f"Paper mapping inventory: 81/81 entries; 4/4 integrations; 8/8 surfaces; {count}/31 remaining closure units open.")
        print(f"Review inputs match {len(data['reviewInputSha256'])} files. Inventory consistency only; no new proofs or completion claim.")
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"Paper mapping inventory error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
