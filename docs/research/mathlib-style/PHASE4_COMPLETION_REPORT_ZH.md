# Mathlib Style Benchmark Phase 4 完成状态报告

**Status：`linux-validation-pending`、`human-review-pending`。**

本地范围内的 16-case pilot、隔离 custody、两路 AI 盲标、裁决、完整 hard-gate
harness 和确定性评分已经实现并通过；由于尚无实际 Linux 运行记录且尚无人类复核，
Phase 4 按验收规则不是真正 complete。

## 1. 目标与范围

本阶段建立独立数据身份 `MATHLIB-STYLE-PILOT-0.1.0`，不改变规则/手册
`v0.3.1`、schema `v0.3.0`、Mathlib `v4.30.0`、Lean 4.30.0、evaluation
environment `MATHLIB-4.30.0` 或 policy snapshot
`MATHLIB-POLICY-2026-08-13`。交付范围包括 16 个真实 primary cases、6 个 PAIR
mirrors、物理隔离的私有标注/Gold/来源/验证、可执行 hard gates、确定性评分和报告。

## 2. 实际新增或修改

Phase 4 新增的公开资产主要为：

- `benchmarks/mathlib-style/cases/{pair,detect,repair,locate}/msb_*/` 下 22 个公开案例目录；
- `manifests/PILOT_CASES.json` 与 `manifests/PUBLIC_SHA256.json`；
- `scripts/phase4_harness.py`、`scripts/score_predictions.py`、
  `scripts/evaluate_repairs.py`、`scripts/check_phase4_provenance.py`、
  `scripts/check_annotation_isolation.py`、`scripts/run_phase4_environment.py`、
  `scripts/check_phase4_preservation.py`、requirements 和评分/静态守卫测试；
- `reports/phase4/BASELINE_SHA256.json`、`RUNBOOK.md`、
  `HUMAN_REVIEW_RUNBOOK.md` 与 `PILOT_REPORT_ZH.md`；
- `.github/workflows/mathlib-style-phase4.yml`（Linux 待实际触发）；
- 本报告以及 README、VERSION、DECISIONS 的非规范性 Phase 4 状态/索引更新。

现有 `check_benchmark.py` 与 `static_lean_guard.py` 仅作 Phase 4 集成扩展。私有
`heldout/private/` 下新增 provenance、annotations、adjudication、gold、reference
repairs、validation specs/records、logs、scoring self-test 和 release manifests，全部
被 Git 忽略。

## 3. 明确未修改的冻结资产

以下内容保持 Phase 4 开始前字节：

- `MANUAL_EN.md`、`MANUAL_ZH.md`、`TAXONOMY.md`；
- 75 个 leaf rule ID、顺序、strength、规范内容和 legacy aliases；
- 11 个 `v0.3.0` schema 的文件名、`$id`、字节数与 SHA-256；
- Phase 2 immutable audit、Phase 3 completion report；
- 3 个 synthetic smoke fixtures 与原 case-policy README；
- Mathlib/environment/policy 固定身份；
- 全部既有 EFG 源码、文档与工作区修改。

开始前的 61 文件基线保存在 `reports/phase4/BASELINE_SHA256.json`；preservation
checker 只允许用户明确要求或 Phase 4 custody 所必需的 7 个 README/VERSION/DECISIONS/harness integration
文件产生 Phase 4 变化，其余捕获文件必须保持原哈希。

## 4. 16 个案例安全摘要

- 任务：PAIR 6、DETECT 4、REPAIR 3、LOCATE 3。
- Strata：Surface 4、Documentation/Statement 4、Proof 4、API/Integration 4。
- 来源：14 `NATURAL_PR`、2 `OFFICIAL_GUIDE_EXAMPLE`、0 synthetic primary。
- Evaluation mode：9 closed context、7 repository agent。
- PAIR mirrors：6；不计入 16 个 primary cases。
- Answerability 安全汇总：13 `ANSWERABLE`、2 `MULTIPLE_ACCEPTABLE`、
  1 `INSUFFICIENT_CONTEXT`。

逐案公开 ID、任务、stratum 和 mode 见
`benchmarks/mathlib-style/reports/phase4/PILOT_REPORT_ZH.md`；不在公开报告中列单案
Gold 或 provenance 定位。

## 5. Source mining 方法

只使用固定 Mathlib checkout、官方 `leanprover-community/mathlib4` PR/review/commit/
source，以及官方 Mathlib style guide。14 个自然案例来自真实 review signal，2 个来自
官方指南示例。每案先保存原始 patch 或固定来源，再移植到 v4.30.0；如果移植会改变
review signal、statement、API 语义或答案，则不纳入 Pilot。

16/16 私有 provenance 均记录 source repository、review reference、base/merge 或
source revision、before/after material、source file/declaration、原始 toolchain、license、
review signal 释义、v4.30.0 差异、逐项 porting change、两端 SHA-256，以及 source、
module、theorem family grouping key。公开 prompt 经扫描不含可反查这些来源的标识。
独立离线 audit 对 14 个自然案例强制 canonical PR、discussion comment 与 merge URL，
并逐字节核对保留 patch、固定 merged-source material、公开 wrapper 与 public JSON 哈希；
2 个官方指南案例绑定 contributor-policy repository、固定 commit 与官方文件哈希。

## 6. Annotation 与 adjudication

在公开案例和 `PUBLIC_SHA256.json` 冻结后建立两个隔离快照。Annotator A 与 B 均为
AI agents，各自只能读取 English manual、RULES/VALIDATORS、16 个公开 primary cases
和任务允许的固定 repository context；它们不能读取 provenance、reference repair、
对方输出、Gold 或 adjudication。

两者各完成 16 份 schema-valid annotation，confidence 分布均为 14 HIGH、2 MEDIUM。
两个隔离快照各保留 76 个允许文件，具有不同的 inventory SHA-256；自动审计核对目录
类别/计数、时间链、confidence、16 个输出及 `saw_other_annotation: false`。
只有两份全部完成后主 agent 才开始逐案裁决。Agreement 为：answerability 15/16、
abstention 16/16、confidence 14/16、finding rule set 14/16、PAIR verdict 6/6、
LOCATE location 3/3；5 案需要实质裁决。16/16 均有 adjudication 与最终 accepted set。

这些是 agent annotations，不是 human annotations；验证记录不把任何 `human.*`
validator 标为已执行。人类复核仍 pending。

## 7. Harness 实现矩阵

| 能力 | 实现 |
|---|---|
| Schema | 标准 `jsonschema` Draft 2020-12 + `referencing` 本地 registry；全部 `$ref` 离线解析 |
| 编译 | 每案独立 compiler 与 text-linter 临时子树、90 秒 timeout、双次 Lean elaboration、规范化输出可复现比较 |
| Forbidden constructs | 静态拒绝 `sorry`、`admit`、候选 `axiom`/`constant`、`native_decide`/等价 trust escape、关键 linter 禁用 |
| Axiom | 目标声明 `#print axioms`；baseline/observed/delta；REPAIR delta hard gate |
| Warnings | standard-linter baseline/observed 分离、case allow-list、unexpected hard failure |
| Validators | Mathlib standard set；真实 text/Unicode/header/style/native-decision linters；compiler；static guard；axiom probe；独立重复 elaboration；2 个适用 LOCATE case 的 `#find_home` evidence；适用 preservation checks |
| REPAIR preservation | 候选重建进 frozen wrapper；editable-region/budget、issue-resolution、双编译、standard/text linter、before/after 声明类型、axiom/warning/no-new-finding gates；reference text 仅诊断 |
| Logs/hashes | compiler/checker/standard/text/axiom/type/location probes 原始日志与 SHA-256；67-file public manifest 与 482-file private custody manifest 分离并互链 |
| Leakage | 递归扫描 `public.json`/README/prompt Lean；拒绝来源/answerability/答案/private-path；严格三文件 public layout、private Git-ignore、无 `.olean`/`.ilean` |
| Scoring | 16-primary 与 mirrors 分离；PAIR verdict/accepted-set/mirror；DETECT precision/recall/F1/priority；REPAIR executable gates/edit cost；LOCATE accepted set；global calibration/rationale 与七维 breakdown；无 LLM judge |

`custom.doc_link_check` 本阶段未实现，也未标记 implemented。`#find_home` 只作为 LOCATE
evidence，不替代 human location judgment；visibility-only LOCATE case 不伪造 tool output。
API/proof 等非确定性判断由 agent annotations 与 adjudication 承担；不伪造人工 validator
状态。本地 checker gate 是记录命令的第二次独立 Lean elaboration；Ubuntu workflow 另
配置实际 `leanchecker`，但尚未运行。

## 8. 本地验证命令与结果

在仓库根目录执行：

```bash
PYTHONPATH=/private/tmp/mathlib-style-jsonschema-runtime \
  python3 benchmarks/mathlib-style/scripts/run_phase4_environment.py \
    --label local-darwin-arm64 --timeout 90
python3 benchmarks/mathlib-style/scripts/check_annotation_isolation.py
PYTHONPATH=/private/tmp/mathlib-style-jsonschema-runtime \
  python3 benchmarks/mathlib-style/scripts/check_phase4_provenance.py
PYTHONPATH=/private/tmp/mathlib-style-jsonschema-runtime \
  python3 benchmarks/mathlib-style/scripts/evaluate_repairs.py \
    --predictions benchmarks/mathlib-style/heldout/private/scoring/perfect_predictions.json \
    --output benchmarks/mathlib-style/heldout/private/scoring/repair-evaluations.json
PYTHONPATH=/private/tmp/mathlib-style-jsonschema-runtime \
  python3 -m unittest discover -s benchmarks/mathlib-style/tests -v
PYTHONPATH=/private/tmp/mathlib-style-jsonschema-runtime \
  python3 benchmarks/mathlib-style/scripts/score_predictions.py \
    --predictions benchmarks/mathlib-style/heldout/private/scoring/perfect_predictions.json \
    --gold-dir benchmarks/mathlib-style/heldout/private/gold \
    --repair-evaluations benchmarks/mathlib-style/heldout/private/scoring/repair-evaluations.json \
    --output benchmarks/mathlib-style/heldout/private/scoring/perfect_score.json
python3 benchmarks/mathlib-style/scripts/check_distillation.py
PYTHONPATH=/private/tmp/mathlib-style-jsonschema-runtime \
  python3 benchmarks/mathlib-style/scripts/check_benchmark.py
python3 benchmarks/mathlib-style/scripts/check_phase4_preservation.py
git diff --check
git status --short --branch
git diff --cached --name-only
```

结果：最终完整私有环境 run 在 Darwin 25.6.0 arm64 上用 1,185.966 秒，identity gate 与
harness exit code 均为 0；22 个公开案例（16 primary + 6 mirrors）在逐案独立 compiler/
text-linter 子树双次编译通过；92 份 schema-governed private JSON 与 22 份 validation
records 通过；axiom delta 全空；unexpected warnings 全空；2/2 适用 location probes、
3/3 executable REPAIR、6/6 mirrors、16/16 单元测试通过。Perfect scorer 以 16 primary
计分，macro/micro 与四任务 score 均为 1.0，mirror 另报 6/6。Public manifest 含 67 个
哈希，private manifest 含 482 个哈希。Benchmark tree 无 `.olean`/`.ilean`；私有目录被
Git ignore，staged 文件数为 0。

## 9. 双环境记录

| 环境 | 身份 | 命令/结果 |
|---|---|---|
| Local | Darwin 25.6.0 arm64；Lean 4.30.0；Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f` | 实际完整 run exit 0；1,185.966 秒；identity/stdout/stderr log SHA-256 与逐案记录在 private custody |
| Linux | 固定 Ubuntu workflow；同 Lean/Mathlib pins | 未实际运行；workflow 已配置 environment evidence artifact，但当前无真实 Linux exit code/log hash |

当前主机没有可用 Linux container/runner；触发 GitHub Actions 需要 push/PR，而任务明确
禁止这些 Git 操作。`.github/workflows/mathlib-style-phase4.yml` 只是可复现入口，不是
Linux 通过证据。

## 10. Public/private custody

公开 `cases/` 和 `PILOT_CASES.json`/`PUBLIC_SHA256.json` 不含 answerability、Gold、
reference repair、canonical A/B mapping、PR/review/commit、adjudication 或 private path。
`heldout/private/` 由 `heldout/.gitignore` 明确忽略；私有 release manifest 关联公开
manifest hash并覆盖 gold、provenance、两路 annotations、adjudication、repairs、validation、
logs、environment evidence 和 scoring assets。Private manifest 位于
`heldout/private/release_manifests/PRIVATE_SHA256.json`，当前精确覆盖 482 个私有资产；
Gold 只在两份 annotations 完成并裁决后生成。

## 11. Git 状态

仍在原分支 `experiment/efg-review-baseline`，跟踪
`fork/experiment/efg-review-baseline`。
开始前已有的大量 EFG tracked modifications 与 untracked
`EFG_Formalization_Exercises.lean` 全部保留；Phase 4 公开内容仍是 untracked
`benchmarks/`、`docs/research/mathlib-style/` 和新 workflow 的一部分。没有 stage、
commit、push、PR、clean、stash、reset 或分支切换；`git diff --cached --name-only`
为空。

## 12. 剩余人工与发布工作

1. 在固定 Linux runner 上实际执行 workflow，并保存 OS/arch、Lean/Mathlib identity、
   命令、exit code 和 log SHA-256 artifact；随后把状态从 `linux-validation-pending`
   更新为真实结果。
2. 由合格人类评审两路 agent annotation、adjudication、source interpretation 和 Gold；
   按公开 `HUMAN_REVIEW_RUNBOOK.md` 生成 ignored private review record；在完成前保持
   `human-review-pending`。
3. 只有 Linux 与 human gates 都通过后，才能评估 release eligibility；当前不得标记
   `Status: complete`，不得宣称公开发布或模型能力结论。
