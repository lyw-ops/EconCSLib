# Mathlib Style Benchmark Phase 5 Readiness 审计

- 审计时间：2026-08-14 12:12:23 +08:00
- 目标 release identity：`MATHLIB-STYLE-PILOT-0.1.0-RC1`
- **Status：`blocked-by-phase4-readiness`**
- Readiness gate：**未通过**
- Gold unseal：**未发生**
- Evaluation agent / prediction / scoring：**均未启动**

## 1. 结论

Phase 5 不能进入冻结、盲测、评分、难度校准、动态红队或 RC1 打包阶段。阻塞不是
16-case inventory、schema、provenance、annotation isolation 或当前 Darwin public
hard gates 的失败，而是 Phase 4 明确仍处于 `linux-validation-pending` 与
`human-review-pending`。Readiness 要求 Phase 4 状态不得为 pending，并要求本地与
Linux hard gates 都有实际通过证据；当前只有 Darwin arm64 的实际 environment record，
没有 Linux run artifact，也没有独立人类复核记录。

此外，任务规定的无环境前缀 preflight 在当前默认 Python 下因缺少 `jsonschema` 失败。
使用 Phase 4 已保留的固定 dependency overlay 后，同一 public harness 与 16 个单元测试
均通过。这个环境问题不会把 Linux 或 human gate 变成通过，且应在下次 readiness 前
标准化。

## 2. Readiness 检查矩阵

| 检查 | 结果 | 实际证据 |
|---|---|---|
| Phase 4 completion report 存在 | PASS | completion-status report 与 public pilot report 均存在 |
| Phase 4 状态非 partial/pending/blocked | **FAIL** | 两份报告均明确写有 `linux-validation-pending`、`human-review-pending` |
| Primary 数量与任务分布 | PASS | 16；PAIR 6、DETECT 4、REPAIR 3、LOCATE 3 |
| 四个 stratum 平衡 | PASS | Surface、Documentation/Statement、Proof、API/Integration 各 4 |
| Synthetic primary | PASS | 14 `NATURAL_PR` + 2 `OFFICIAL_GUIDE_EXAMPLE`，0 synthetic |
| Public case schema/layout/hash | PASS | 22 个 public case（含 6 mirrors）、严格三文件布局、67 个 public hashes |
| Private schema/custody manifest | PASS | 92 个 schema-governed documents；482-file custody manifest 一致 |
| Source provenance | PASS | 16/16 离线 provenance audit 通过 |
| 两份独立 annotation | PASS | 两个不同的 76-file snapshot，各 16 输出，无跨标注可见性 |
| Adjudication / Gold / validation inventory | PASS | 保留的 2 份 adjudication、22 Gold、22 validation records 结构完整 |
| Public/private leakage | PASS | public harness 的递归 leakage、layout、hash 与 mirror 检查通过 |
| 本地 hard gates | PASS | 当前 Darwin public 重跑：22/22 重复编译；保留的 full-private Darwin record 为 PASSED |
| Linux hard gates | **FAIL** | 无实际 Linux environment record、exit code 或 log-hash artifact |
| 独立人类复核 | **FAIL** | 无 human-review record；Phase 4 仍明确标记 pending |
| Mirrors 不计入 primary | PASS | 6 个 mirror 与 16 primary 分离 |
| Private custody 被 Git ignore | PASS | `git check-ignore` 命中 committed held-out policy |
| Benchmark tree 无 `.olean` / `.ilean` | PASS | 扫描无结果 |
| Phase 3 固定资产无漂移 | PASS | distillation 与 preservation checks 通过；75 rules、aliases、11 schemas 保持 |
| 默认 Python preflight runtime | **FAIL** | 默认解释器缺 `jsonschema`；固定 dependency overlay 下通过 |

公开 manifest SHA-256 为
`bccd572e26baf8ab438d6bde263b03a0e260eda0be4e3347946a60fcbf792b43`。本报告只记录
private custody 的安全计数，不披露 private gold/provenance/validation 的逐文件哈希或
内容。

## 3. 实际运行结果

首次按原样执行规定 preflight：

- `check_distillation.py`：通过；75 rules、11 frozen schemas 与固定资产一致；
- `check_benchmark.py`：因默认 Python 缺少 Phase 4 `jsonschema` runtime 而失败；
- `unittest discover`：16 个测试中 15 个完成、1 个因同一缺失依赖报错。

使用 Phase 4 已固定的本地依赖后重新运行：

- scorer/static-guard tests：16/16 通过；
- Phase 4 preservation：54 个 captured files 未变，7 个预期 integration files 保持；
- provenance：16/16 通过，14/2/0 source-class 分布正确；
- annotation isolation：两个不同的 76-file snapshots，各 16 输出，隔离通过；
- benchmark/public hard gates：3 smoke cases、4 fixture Lean files 通过；16 primary +
  6 mirrors、22 repeated compilations、67 public hashes 全部通过；
- private schema validation：92 documents 通过；private custody manifest 覆盖 482 files
  且一致；
- benchmark tree：无 `.olean` 或 `.ilean`。

这些结果确认当前 Darwin/public 与保留的 local private 证据仍一致，但不能替代实际
Linux run，也不能替代合格人类复核。

## 4. 阻塞项与解除条件

1. 在固定 Linux runner 上针对同一 public manifest 实际运行 Phase 4 gates，保存
   OS/architecture、Lean/Mathlib identity、完整命令、exit code 与 log SHA-256。
2. 按 `HUMAN_REVIEW_RUNBOOK.md` 完成独立、合格的人类复核，并在 ignored private
   custody 中保存完整 review record。
3. 仅在上述证据针对未变的冻结 hashes 成立后，才可把 Phase 4 状态从 pending 更新为
   非 pending 的真实状态。
4. 为规定的无前缀 Python 命令安装固定 requirements，或把固定 dependency overlay
   标准化为可复现入口。
5. 完成后重新运行 Phase 5 readiness audit。旧审计不得直接改写为 PASS。

## 5. 协议保护

由于 readiness 失败，本次没有创建：

- `SCORING_PROTOCOL.json`；
- Phase 5 public/private freeze manifests；
- evaluation runs、predictions 或 prediction freeze；
- scoring、difficulty、red-team result 或 release archive；
- `pilot-0.1.0-rc1/` release 目录。

主 agent 没有打开、打印、重写或 unseal private gold，也没有启动 evaluation/red-team
subagent。Phase 5 后续状态必须保持 `blocked-by-phase4-readiness`，直至新的 readiness
审计实际通过。
