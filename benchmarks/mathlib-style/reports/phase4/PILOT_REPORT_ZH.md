# Mathlib Style Benchmark Phase 4 Pilot 报告

- Pilot identity：`MATHLIB-STYLE-PILOT-0.1.0`
- Rule/manual：`v0.3.1`
- Data schema：`v0.3.0`
- Evaluation environment：`MATHLIB-4.30.0`
- Status：`linux-validation-pending`、`human-review-pending`
- 日期：2026-08-13

本报告只提供不会揭示单案答案的公开汇总。Gold、来源定位、A/B canonical
mapping、reference repair、逐案验证日志和裁决细节均留在 Git 忽略的私有
custody 中。

## 1. Pilot 构成

Pilot 恰有 16 个 primary cases；6 个 PAIR mirror 只用于方向一致性检查，不计入
primary 数量。

| 任务 | Primary 数量 | Mirror 数量 |
|---|---:|---:|
| PAIR | 6 | 6 |
| DETECT | 4 | 0 |
| REPAIR | 3 | 0 |
| LOCATE | 3 | 0 |
| 合计 | 16 | 6 |

| Stratum | 数量 |
|---|---:|
| Surface | 4 |
| Documentation / Statement | 4 |
| Proof | 4 |
| API / Integration | 4 |

安全的 primary 索引如下。它只列出公开字段，不列答案或来源定位。

| ID | Task | Stratum | Evaluation mode |
|---|---|---|---|
| `msb_p001` | PAIR | Surface | Closed context |
| `msb_p002` | PAIR | Surface | Closed context |
| `msb_d001` | DETECT | Surface | Closed context |
| `msb_r001` | REPAIR | Surface | Closed context |
| `msb_p003` | PAIR | Documentation / Statement | Closed context |
| `msb_d002` | DETECT | Documentation / Statement | Repository agent |
| `msb_r002` | REPAIR | Documentation / Statement | Closed context |
| `msb_p004` | PAIR | Documentation / Statement | Closed context |
| `msb_p005` | PAIR | Proof | Closed context |
| `msb_d003` | DETECT | Proof | Closed context |
| `msb_r003` | REPAIR | Proof | Repository agent |
| `msb_p006` | PAIR | Proof | Repository agent |
| `msb_d004` | DETECT | API / Integration | Repository agent |
| `msb_l001` | LOCATE | API / Integration | Repository agent |
| `msb_l002` | LOCATE | API / Integration | Repository agent |
| `msb_l003` | LOCATE | API / Integration | Repository agent |

来源类别为 14 个 `NATURAL_PR` 和 2 个 `OFFICIAL_GUIDE_EXAMPLE`，0 个
synthetic primary case。私有 answerability 安全汇总为：13 个 `ANSWERABLE`、
2 个 `MULTIPLE_ACCEPTABLE`、1 个 `INSUFFICIENT_CONTEXT`。Pilot 包含真实
PAIR `TIE`、仓库上下文与 closed context、编译成功但 linter 可判定的问题、
statement/API、proof reuse/structure 和 import/location 覆盖。

## 2. Provenance 与隔离

16/16 primary cases 均有 schema-valid 私有 provenance。`NATURAL_PR` 记录包含
source repository、PR/review 定位、base/merge 或 patch 身份、source declaration、
原始 toolchain、license、review signal 释义、v4.30.0 差异、全部移植修改、移植前后
SHA-256，以及 source/module/theorem family grouping key。官方指南案例同样记录固定
官方来源与移植哈希。离线 provenance audit 实际复核 16/16 覆盖、14/2/0 分布、
canonical PR/comment/commit URL、保留 patch 哈希、固定 source-material 哈希和公开
ported-wrapper 哈希。

公开目录只含 `public.json`、prompt 和 README；私有目录由
`benchmarks/mathlib-style/heldout/.gitignore` 屏蔽。公开 manifest 只冻结公开资产，
private custody manifest 单独冻结 gold、provenance、annotation、adjudication、repair、
validation 和 logs。公开 leakage 扫描拒绝 PR/URL、review/commit、answerability、gold、
reference repair、private path、adjudication 和直接答案字段。

## 3. 盲标与裁决

公开 prompt 和规范冻结后，两个隔离 AI agents 分别只获得 `v0.3.1` English manual、
RULES/VALIDATORS、16 个公开 primary prompts 和任务允许的固定 repository context。
它们未获得 provenance、reference repair、另一方输出、Gold 或 adjudication。

- Annotator A：16/16；14 `HIGH`、2 `MEDIUM`、0 `LOW`。
- Annotator B：16/16；14 `HIGH`、2 `MEDIUM`、0 `LOW`。
- 两份 annotation 均通过 `annotation.schema.json`。
- 两个保留的隔离快照各含 76 个文件（48 个 case assets、3 个 guidance、2 个 schema、
  7 个 repository-context、16 个自有输出）；inventory hash 不同，自动审计未发现跨标注可见性。
- 两份完成后才进行逐案 adjudication；16/16 均有最终决定，其中 5 案需要实质判断。

Exact agreement：answerability 15/16，abstention 16/16，confidence 14/16，finding
rule set 14/16，PAIR verdict 6/6，LOCATE locations 3/3；3 个 REPAIR 的修复意图在
裁决后均一致。以上是 AI-agent agreement，不是 human agreement。

## 4. Hard gates

| Gate | 本地结果 |
|---|---|
| Draft 2020-12 schema + 本地 `$ref` | 通过 |
| 公开 inventory、任务/stratum、mirror 计数 | 通过 |
| 每案独立 compiler/text-linter 临时子树、双次 Lean elaboration、90 秒 timeout | 22/22 通过 |
| Mathlib standard linter set | 22/22 通过允许策略 |
| Mathlib text/Unicode linter | 22/22 通过 |
| `sorry` / `admit` / `axiom` / `constant` / trust escape / linter-disable 扫描 | 通过 |
| 目标声明 `#print axioms` baseline/observed/delta | 22/22 delta 为空 |
| Warning baseline/observed/allow-list | 22/22 无意外 warning |
| 适用 `#find_home` location evidence | 2/2 LOCATE cases 通过；visibility-only case 不冒充 location-tool 判定 |
| REPAIR executable reference + statement type preservation | 3/3 通过 |
| Provenance、annotation-isolation、public/private SHA-256、ignore 与 recursive leakage | 通过；67 public + 482 private hashes |
| PAIR mirror transformation/consistency | 6/6 通过 |
| 私有 executable REPAIR perfect fixture | 3/3 通过；reference text 仅诊断 |
| 私有 perfect-prediction scorer self-test | 16 primary + 6 mirrors；macro/micro/task score 均为 1.0 |
| Scorer/static-guard 单元测试 | 16/16 通过 |

验证记录不会把 `human.*` validator 标为已执行；人工复核仍是独立发布门禁。
适用但不具确定性自动执行契约的 API、proof、location 判断由两路 agent annotation
和 adjudication 记录，不伪装为自动 validator。

## 5. 确定性 primary metrics

- PAIR：verdict、accepted set、mirror consistency；mirror 不计 primary 数量。
- DETECT：leaf-rule precision/recall/F1、declaration-aware span overlap；priority 单列。
- REPAIR：compile、issue resolution、statement/interface preservation、无新增 finding、
  axiom/warning gates 和 edit cost；exact reference text 不是主要指标。
- LOCATE：accepted location / accepted set、abstention 与 insufficient-context。
- Global：answerability、abstention calibration、unsupported-rationale rate，并按 task、
  stratum、source class 与 evaluation mode 分层。

Primary score 全部由确定性程序计算，不使用 LLM judge。评分单元测试覆盖正确/错误、
tie、multiple acceptable、insufficient context、空 finding、部分 span 重叠和无效 prediction。

## 6. 双环境结果与限制

| 环境 | 结果 | 证据 |
|---|---|---|
| 本地 Darwin 25.6.0 arm64；Lean 4.30.0；Mathlib 固定 commit | 通过 | 完整私有 run exit 0，1,185.966 秒；identity/stdout/stderr SHA-256；22 validation records 与 482-asset custody manifest |
| 固定 Ubuntu GitHub Actions | 未实际运行 | workflow 将生成并上传 OS/arch、identity、command、exit code 与 log-hash evidence；目前无真实 artifact |

当前 Linux runner 不可用，而任务明确禁止 push/PR，因此无法触发实际 GitHub Actions。
此外两份标注均为 AI agent 输出，尚无人类复核。故 Pilot 只能标记为
`linux-validation-pending` 与 `human-review-pending`，不能标记 `complete`、不能声明
public-release eligible，也不能用于模型能力结论。
