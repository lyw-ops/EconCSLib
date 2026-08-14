# Mathlib Style Distillation Phase 1 完成报告

- **日期：** 2026-08-13
- **Outcome：** 完成
- **范围：** Repository Integration
- **Benchmark 状态：** 未完成、未发布

## 1. Outcome

Phase 1 已完成。正式文档和 benchmark 目录已经集成，完整 v0.3.0 schemas 已从
可验证 artifact 恢复，静态检查、标准 JSON Schema validation 和固定 Lean/Mathlib
smoke compilation 均通过。旧根 `mathlib-style-distillation/` 在迁移前后比较和
验证通过后移除。

本结论只适用于仓库集成阶段，不表示正式 benchmark、pilot 或 full harness 已完成。

## 2. Changed paths

### 修改

- 根 `AGENTS.md`：仅增加 4 行 Mathlib Style 入口。

### 新建

- `docs/research/mathlib-style/`：
  - `README.md`；
  - `MANUAL_EN.md`；
  - `MANUAL_ZH.md`；
  - `TAXONOMY.md`；
  - `DECISIONS.md`；
  - `VERSION.md`；
  - `REPOSITORY_INTEGRATION_ZH.md`；
  - 本报告。
- `benchmarks/mathlib-style/`：
  - `AGENTS.md` 和 `README.md`；
  - `evidence/` 下六个 retrieval indexes、counterexample policy 和空白 audit target；
  - `cases/pair|detect|repair|locate/` policy placeholders；
  - `fixtures/positive|negative|repair/` smoke fixtures；
  - `heldout/` custody policy；
  - `manifests/` 下四个 registries、环境 manifest 和 schema set；
  - `scripts/` 下 static guard、结构检查和 smoke compiler。

### 恢复的 schemas

`benchmarks/mathlib-style/manifests/schemas/` 包含：

- 11 个原样复制的 `*.schema.json`；
- `MANIFEST.json`：保存原 artifact 的 byte count 和 SHA-256；
- `README.md`：记录 provenance、作用域和验证方式。

### 删除

- 旧未跟踪 `mathlib-style-distillation/`：只在资产对照与新结构验证通过后删除。

没有 stage、commit、push 或创建 PR。

## 3. Preserved invariants

| Invariant | Result |
|---|---:|
| 唯一 leaf rule IDs | 75 |
| naming | 12 |
| statements（`FMT-*`、`STM-*`） | 24 |
| api | 7 |
| proofs | 7 |
| documentation | 13 |
| imports/file structure | 12 |
| Rule strengths | `MUST/SHOULD/PREFER/CONTEXT` |
| Finding priorities | `BLOCKING/SUBSTANTIVE/MINOR/INFORMATIONAL` |
| Task union | `PAIR/DETECT/REPAIR/LOCATE` |
| Evidence anchors | 10 |
| Synthetic smoke fixtures | 3 |
| Lean fixture files | 4 |
| Frozen schemas | 11 |

固定身份：

- Mathlib：`v4.30.0`；
- Mathlib commit：`c5ea00351c28e24afc9f0f84379aa41082b1188f`；
- Lean：`leanprover/lean4:v4.30.0`；
- Policy snapshot：`MATHLIB-POLICY-2026-08-13`；
- Policy commit：`7b967eb1aaab674bd6aead708d42c4a83e2aca05`。

迁移比较确认：

- 旧、新 75 个 rule ID 集合完全相同；
- `RULES/SOURCES/VALIDATORS/COVERAGE` registries 字节相同；
- 10 个 evidence records 在重分类后内容相同；
- smoke fixture 目录内容相同；
- held-out policy 和 static guard 相同；
- 11 个正式 schema 文件与原 artifact 字节相同。

## 4. Validation

### Structural and integrity

```bash
python3 benchmarks/mathlib-style/scripts/check_distillation.py
```

结果：

```text
75 rules
10 evidence anchors
3 smoke cases / 4 Lean files
pinned Mathlib checkout verified
11 frozen v0.3.0 schemas hash-verified and reference-checked
```

该检查覆盖目录、registries、rule vocabulary、task union、Manual/Taxonomy
coverage、index partition、Markdown links、schema manifest/hash/shape/`$ref`、
evidence commit/blob/line range、fixture metadata、held-out custody 和 static guard。

### Standard JSON Schema validation

使用临时安装在 `/tmp` 的标准 `jsonschema==4.25.1` Draft 2020-12 validator：

- 11 个 schemas 全部通过 metaschema `check_schema`；
- 原 artifact 的 12 个 validation examples 全部通过对应 schema；
- 该临时 validator 未加入或改变仓库依赖。

### Pinned Lean smoke compilation

```bash
python3 benchmarks/mathlib-style/scripts/check_benchmark.py
```

结果：

```text
3 cases
4 Lean files
Lean 4.30.0
all compiled
no unexpected warnings
```

### JSON and whitespace

```bash
python3 <JSON/JSONL parse audit>
git diff --check
```

结果：

- 31 个 JSON/JSONL 文件解析通过；
- diff whitespace check 通过；
- 旧目录不存在；
- 没有残留的错误 schema blocker 或 Phase 1 未完成状态声明。

### Git isolation

```bash
git status --short --branch
git diff -- AGENTS.md
```

结果：

- 根 `AGENTS.md` 仅新增短入口；
- Mathlib Style 文件只出现在两个正式目标目录；
- 既有 EFG 文件仍保持进入本任务前的 dirty 状态，没有被本任务编辑或清理。

## 5. Unresolved blockers

Phase 1 没有未解决 blocker：

- schemas：完整恢复并验证；
- evidence：全部 10 个 anchors 在固定 checkout 验证；
- fixed environment：可用并验证；
- legacy directory：验证后已移除。

以下是后续阶段工作，不是 Phase 1 blocker：

- Manual adversarial audit；
- full style-linter/axiom/warning/statement-preservation/scoring harness；
- 16 个正式 pilot cases；
- 两位独立 annotator 和 adjudication；
- baseline model evaluation。

## 6. Scope confirmation

- 没有修改、覆盖、格式化或清理既有 EFG Lean 源码。
- 没有修改既有 EFG 文档或 EFG scripts。
- 没有修改 `EFG_Formalization_Exercises.lean`。
- 没有执行 reset、restore、checkout、clean 或 stash。
- 没有 stage、commit、push 或创建 PR。
- 没有开始 Manual adversarial audit；audit 文件仍是空白 scope marker。
- 没有修改 75 条规则的规范内容或强度。
- 没有创建虚假的正式 pilot cases。
- 没有声称 Mathlib Style Benchmark 已完成或发布。
