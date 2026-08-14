# Mathlib Style Distillation Phase 3 完成报告

- **报告日期：** 2026-08-13
- **状态：** 完成（13/13 规范 finding 已处理，全部规定验证通过）
- **规则/手册 artifact：** `v0.3.1`
- **Benchmark data schema：** `v0.3.0`（不变）
- **评测环境：** Mathlib `v4.30.0` / `c5ea00351c28e24afc9f0f84379aa41082b1188f` / Lean `leanprover/lean4:v4.30.0`
- **政策快照：** `MATHLIB-POLICY-2026-08-13` / `7b967eb1aaab674bd6aead708d42c4a83e2aca05`

## 1. 目标与范围

本阶段以不可变的 Phase 2 `v0.3.0` manual adversarial audit 为输入，逐条
解决其中 13 条 P1/P2 finding，并把修订同步到规范手册、rule taxonomy、
machine-readable rule/source/validator/coverage registries 与结构检查器。

本阶段是规范补丁，不是 benchmark data schema migration，也不是 benchmark
生产。75 个 leaf rule ID、legacy aliases、`PAIR` / `DETECT` / `REPAIR` /
`LOCATE` 任务定义、固定环境与政策身份全部保留；不创建正式 case、训练数据、
测试数据或 held-out gold。

## 2. 13 条 finding 处置矩阵

“强度/自动化”栏使用 `before → after`；相同值表示保留元数据但收窄文字或
验证边界。

| Rule | Phase 2 disposition | 强度 | 自动化 | v0.3.1 文字处置 | Validator/source 变化 | Benchmark 标签影响 |
|---|---|---|---|---|---|---|
| `FIL-003` | `REQUIRES_QUALIFICATION` | `SHOULD → SHOULD` | `ASSISTED → ASSISTED` | 排序只约束普通 public/ordinary import 区块；不为少见 modifier 臆造全序。 | 无 ID 变化；保留 header 与 custom order evidence。 | 普通区块内可判错；`public meta import`/`import all` 相对顺序不得自动判错。 |
| `FIL-008` | `STRENGTH_TOO_STRONG` | `MUST → MUST` | `DETERMINISTIC → ASSISTED` | 硬禁 `Mathlib.Tactic` 与明确禁止项；`Lake.*` 改为必要性、性能与 allowance 评审。 | 增加 `human.location_review`；固定 `LIN-HEADER`。 | bucket import 保持硬负例；有完整理由的 `Lake.*` 不是无条件失败。 |
| `FMT-005` | `SCOPE_TOO_BROAD` | `SHOULD → SHOULD` | `HUMAN → HUMAN` | 只在省略妨碍公共签名可读性/API 含义时要求显式类型；允许 typed dependent context 中可推断 binder。 | 无 validator/source 变化。 | `{n}`/`{m}` 等清楚可推断 binder 是合法例外。 |
| `FMT-011` | `SCOPE_TOO_BROAD` | `SHOULD → SHOULD` | `DETERMINISTIC → ASSISTED` | 写明 empty-line linter 的 syntax/path 排除项与 incomplete-command 边界。 | 增加 `human.layout_review`；固定 `LIN-EMPTY`。 | 只有 linter 实际覆盖范围可用 deterministic 标签，其他为 assisted/human。 |
| `FMT-012` | `REQUIRES_QUALIFICATION` | `MUST → MUST` | `DETERMINISTIC → ASSISTED` | 枚举实际 development、unscoped、deprecated 与 debt option 类别；其他技术 option 按作用域/理由评审。 | 增加 `human.layout_review`；固定 `LIN-STYLE`。 | 不再把所有 production `set_option` 标成失败；测试与窄作用域技术例外单列。 |
| `FMT-019` | `REQUIRES_QUALIFICATION` | `MUST → MUST` | `ASSISTED → ASSISTED` | 字符/variant 合法性与数学可读性分离，并声明 allow-list 依赖快照。 | `custom.unicode_allowlist` 改为真实 `linter.unicodeLinter`；增加 `LIN-TEXT-BASED`、`LIN-UNICODE` 固定 blob。 | 机器标签只覆盖固定快照合法性；可读性仍为人工标签。 |
| `DOC-001C` | `REQUIRES_QUALIFICATION` | `SHOULD → SHOULD` | `HUMAN → HUMAN` | `Main definitions/statements` 明确为 optional；`Notation/References/Tags` 只在相关时要求。 | 无 validator/source 变化。 | 只有内容相关时才把 conditional section 缺失标成 finding。 |
| `DOC-002C` | `STRENGTH_TOO_WEAK` | `SHOULD → SHOULD` | `HUMAN → HUMAN` | 明确新显式 field 默认应有 docstring，并列 generated、extends-only、真正自明的有限例外。 | 无 validator/source 变化。 | 未文档化的新 law/data field 默认违规；无新增字段等例外不得误报。 |
| `DOC-004` | `REQUIRES_QUALIFICATION` | `SHOULD → SHOULD` | `ASSISTED → ASSISTED` | 把 docstring delimiter/空白等机械检查与句号、boldface、文风人工评审分离。 | 保留 `linter.style.docString` + human review，固定 `LIN-DOCSTYLE` 边界。 | deterministic syntax 标签与 human prose 标签必须拆开。 |
| `DOC-005` | `REQUIRES_QUALIFICATION` | `SHOULD → SHOULD` | `ASSISTED → ASSISTED` | 使用真实 Lean 4 FQ name `Set.mem_iUnion₂`；明确 backtick 不等于解析成功及各种名称解析边界。 | 从该规则移除不负责解析的 `linter.style.docString`；`custom.doc_link_check` 明示为未实现的 planned check。 | exact FQ name、namespace/protected/alias/ambiguous/unresolved 分开评测。 |
| `PRF-007` | `REQUIRES_QUALIFICATION` | `MUST → MUST` | `DETERMINISTIC → DETERMINISTIC` | 保留 trust 禁令，披露 syntax linter false negative，并加入真实 checker gate。 | 增加 `checker.leanchecker` 与 `CI-LEANCHECKER`；命令固定为 `lake env leanchecker --fresh Mathlib`。 | syntax-linter 通过不能单独接受；硬标签还需 checker evidence。 |
| `API-007` | `STRENGTH_TOO_WEAK` | `CONTEXT → SHOULD` | `ASSISTED → ASSISTED` | 普通适用场景提升为 SHOULD，同时保留 existing companion、unsupported constant、naming override、API hazard 等例外。 | 无 validator/source 变化。 | 普通缺失 parity 可报 SHOULD finding；列明的 transformation 例外不得误报。 |
| `LOC-002A` | `REQUIRES_QUALIFICATION` | `SHOULD → SHOULD` | `ASSISTED → ASSISTED` | 区分 `#min_imports in` 向上单 command 实验与 `linter.minImports` 从激活点向下增量跟踪。 | 保留两个工具与 human review，并固定各自源码 blob。 | 工具输出与架构判断分开；两者均不能证明全局 import 最小性。 |

处置结果：**13/13 finding 已进入 `v0.3.1` 规范与 machine metadata；0 条
延期，0 个新增/删除/重命名 leaf rule ID。**

## 3. 版本边界

- `RULES.json.version`、`SOURCES.json.registry_version`、
  `VALIDATORS.json.registry_version`、`COVERAGE.json.version` 与双语手册版本为
  `0.3.1`。
- `RULES.json.schema_version` 继续为 `0.3.0`。
- `manifests/schemas/` 下 11 个 schema、其 `$id`、byte count 与 SHA-256
  保持 `v0.3.0` 原始 contract，不迁移、不规范化、不放宽。
- Phase 2 audit 继续描述它实际审计的 `v0.3.0`，SHA-256 为
  `6de8679ad90d88a48f6ad792ee1fcd54046c10f647c8d8a813c211db772bf48a`。

## 4. 实际修改文件

1. `docs/research/mathlib-style/README.md`
2. `docs/research/mathlib-style/MANUAL_EN.md`
3. `docs/research/mathlib-style/MANUAL_ZH.md`
4. `docs/research/mathlib-style/TAXONOMY.md`
5. `docs/research/mathlib-style/VERSION.md`
6. `docs/research/mathlib-style/DECISIONS.md`
7. `docs/research/mathlib-style/PHASE3_COMPLETION_REPORT_ZH.md`（新增）
8. `benchmarks/mathlib-style/README.md`
9. `benchmarks/mathlib-style/manifests/RULES.json`
10. `benchmarks/mathlib-style/manifests/SOURCES.json`
11. `benchmarks/mathlib-style/manifests/VALIDATORS.json`
12. `benchmarks/mathlib-style/manifests/COVERAGE.json`
13. `benchmarks/mathlib-style/scripts/check_distillation.py`

## 5. 明确未修改的资产

- `benchmarks/mathlib-style/evidence/audits/manual_adversarial_audit.md`；
- `benchmarks/mathlib-style/manifests/schemas/` 的 manifest、README 与全部 11
  个 schema；
- `benchmarks/mathlib-style/fixtures/` 的 3 个 synthetic smoke case manifest
  与 4 个 Lean fixture；
- `benchmarks/mathlib-style/cases/{pair,detect,repair,locate}/`；
- `benchmarks/mathlib-style/heldout/`；
- evidence 的 category indexes、`EXAMPLES.jsonl` 与 counterexample materials；
- `manifests/mathlib-4.30.md`、`scripts/check_benchmark.py`、
  `scripts/static_lean_guard.py`；
- EconCSLib Lean 源码、EFG 架构工作及仓库中其他已有未提交改动。

## 6. 结构检查器强化

`check_distillation.py` 现在额外强制：artifact/schema 双版本边界、固定 75
ID 与 legacy aliases、13 条修订元数据/文字 anchor、双语手册逐行与
`RULES.json` 一致、真实 Unicode/checker validator contract、完整固定
source path/blob、Phase 2 audit/fixtures/cases/heldout 哈希、11 schema 完整性，
以及 benchmark tree 下不得残留 `.olean`/`.ilean`。

## 7. 验证记录

全部验证于 2026-08-13 从仓库根目录执行并通过：

```bash
python3 benchmarks/mathlib-style/scripts/check_distillation.py
python3 benchmarks/mathlib-style/scripts/check_benchmark.py
git diff --check
git status --short --branch
```

- `check_distillation.py`：退出码 0；确认 75 rules、10 evidence anchors、3
  smoke cases/4 Lean files、14 个 fixed machine sources、11 个冻结
  `v0.3.0` schemas，以及 14 个 Phase 2/case/fixture/held-out 固定文件；本地
  Mathlib checkout commit 与全部 registry blob 均匹配。
- `check_benchmark.py`：退出码 0；3 cases、4 Lean files 在 Lean 4.30.0 下
  smoke 编译通过，并继续明确 full hard gates/task scoring 尚未实现。
- 独立 JSON/JSONL 解析：25 个 JSON、6 个 JSONL 全部成功。
- `git diff --check`：退出码 0；对本阶段 13 个新增/修改文件另用尾随空白
  扫描复核，无匹配。
- benchmark tree 生成物扫描：无 `.olean` 或 `.ilean`。
- Phase 3 前后 SHA-256 inventory 对比：恰有下节列出的 12 个既有文件变化、
  1 个报告新增、0 个文件删除；Phase 2 audit、schemas、fixtures、cases 与
  heldout 均保持原哈希。
- 结构检查器另行确认 75 个 ID 的集合与顺序、6 组 legacy aliases、task
  union、双语手册表格、13 条 finding expectation、artifact/schema 双版本
  和真实 Unicode/checker contract。

## 8. Phase 4 待办

Phase 4 仍需完成：16 个真实可追溯 pilot case 的 source mining；公开 prompt
与 private gold/provenance/validation 的物理分离；两名独立标注者与
adjudication；完整 linter/warning/axiom-delta/statement-preservation/scoring
harness；两环境验证、leakage 检查与 held-out 评测。当前 3 个
`SYNTHETIC_SMOKE` case 只验证布局、metadata、静态 guard 与基本编译，不能
支持模型能力或正式 benchmark 完成度声明。

## 9. Git 状态边界

最终 `git status --short --branch` 显示分支为
`experiment/efg-review-baseline...fork/experiment/efg-review-baseline`。工作树在
本任务开始前已有大量 tracked EFG/设计文档修改、`AGENTS.md` 修改，以及
`EFG_Formalization_Exercises.lean`、`benchmarks/`、
`docs/research/mathlib-style/` 等 untracked 路径；Phase 3 文件因此在简短状态
中聚合显示在两个 untracked 目录下。

`git diff --cached --name-only` 为空。本阶段没有 stage、commit、push、清理
或删除操作，也没有改写任何无关 EFG 工作。
