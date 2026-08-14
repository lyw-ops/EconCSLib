# Mathlib Style Distillation：架构结论与仓库集成状态

- **状态日期：** 2026-08-13
- **Phase 1：** 完成
- **Artifact version：** `v0.3.0`
- **Benchmark maturity：** 未完成、未发布
- **本文性质：** 架构结论、完成状态与后续边界；不是风格规范

## 1. Outcome

Mathlib Style Distillation Phase 1（Repository Integration）已经完成。

正式资产现位于：

- `docs/research/mathlib-style/`；
- `benchmarks/mathlib-style/`。

迁移保留了：

- 75 个唯一 leaf rule ID；
- `MUST/SHOULD/PREFER/CONTEXT` 规则强度；
- `BLOCKING/SUBSTANTIVE/MINOR/INFORMATIONAL` finding priority；
- `PAIR/DETECT/REPAIR/LOCATE` 四类任务；
- rules、sources、validators、coverage registries；
- 10 个固定 Mathlib commit/blob/行号的 evidence anchors；
- 3 个公开 synthetic smoke fixtures 和 4 个 Lean 文件；
- public/private benchmark 隔离设计；
- 固定环境、provenance、hash 和完整验证门槛；
- 完整的 11 个 v0.3.0 JSON Schemas。

旧的根 `mathlib-style-distillation/` 只在新结构通过迁移前后比较、静态检查和
固定环境 smoke compilation 后移除。

Phase 1 完成不表示 benchmark 已完成。正式 pilot cases、full harness、独立标注、
adjudication 和 Manual adversarial audit 仍属于后续阶段。

## 2. 架构结论

采用 EconCSLib 仓库集成结构，同时保留 v0.3.0 更严格的数据和验证模型，是比独立
根目录更好的方案：

1. 根 `AGENTS.md` 只保留简短入口；
2. 人类可读规范归入 `docs/research/mathlib-style/`；
3. benchmark 行为、evidence、cases、fixtures、manifests 和 scripts 归入
   `benchmarks/mathlib-style/`；
4. `MANUAL_EN.md`、`TAXONOMY.md` 和 `RULES.json` 各有单一职责；
5. Evaluation Mode 与 Distillation/Audit Mode 明确分离；
6. visible fixtures 与 formal cases 明确分离；
7. formal cases 按任务类型组织，而不按 positive/negative 泄漏答案。

未采用 H/S/P/X 替换原规则强度。规则强度、finding priority、evidence class 和
counterexample classification 保持为不同维度。

## 3. Authority modes

### Evaluation Mode

`MANUAL_EN.md` 是 normative specification。`MANUAL_ZH.md` 只作解释，
`TAXONOMY.md` 是人类可读索引，规则的机器身份仍由 `RULES.json` 定义。

编译通过只证明最低限度的 Lean 接受性，不能替代：

- logical correctness；
- mathematical fidelity；
- API appropriateness；
- Mathlib style conformity；
- maintainability。

### Distillation / Audit Mode

审计 Manual 时，以固定 Mathlib `v4.30.0` 源码、独立固定的 policy snapshot 和
validator behavior 为 empirical evidence。Manual 不能证明自身。

发现反例后，应分类为：

- `GENUINE_COUNTEREXAMPLE`；
- `LEGITIMATE_EXCEPTION`；
- `DOMAIN_SPECIFIC`；
- `COMPATIBILITY_CONSTRAINT`；
- `GENERATED_CODE`；
- `LEGACY_CODE`；
- `INCONCLUSIVE`。

Phase 1 仅建立了空白 audit target，没有开始规则审计或修改 Manual 内容。

## 4. 正式目录状态

### Documentation

`docs/research/mathlib-style/` 包含：

- `README.md`；
- `MANUAL_EN.md`；
- `MANUAL_ZH.md`；
- `TAXONOMY.md`；
- `DECISIONS.md`；
- `VERSION.md`；
- 本集成状态报告。

`TAXONOMY.md` 精确覆盖 75 条 leaf rules，每条规则的 title、strength、
evidence class 和 automation level 均与 `RULES.json` 对照验证。

### Benchmark assets

`benchmarks/mathlib-style/` 包含：

- benchmark-specific `AGENTS.md` 和 `README.md`；
- 六个 evidence retrieval indexes；
- counterexample policy 和空白 adversarial-audit target；
- 四个 formal task 目录；
- 三类 visible smoke fixtures；
- held-out custody policy；
- registries、环境 manifest 和 schemas；
- static guard、结构检查和固定环境 smoke compiler。

### Rule partition

| Retrieval index | Rule families | Count |
|---|---|---:|
| naming | `NAM-*` | 12 |
| statements | `FMT-*`、`STM-*` | 24 |
| api | `API-*` | 7 |
| proofs | `PRF-*` | 7 |
| documentation | `DOC-*` | 13 |
| imports | `FIL-*`、`LOC-*` | 12 |
| **Total** | all leaf rules | **75** |

六个 indexes 是旧五类分区的细化；它们不构成新的规范 authority。

## 5. Schema recovery

完整 v0.3.0 schemas 已从提供的 `mathlib_style_v0.3.0 3` artifact 恢复，而非
重建。共 11 个 JSON Schema Draft 2020-12 文件：

1. `annotation.schema.json`；
2. `common.schema.json`；
3. `detect-case.schema.json`；
4. `locate-case.schema.json`；
5. `pair-case.schema.json`；
6. `prediction.schema.json`；
7. `private-gold.schema.json`；
8. `private-provenance.schema.json`；
9. `public-case.schema.json`；
10. `repair-case.schema.json`；
11. `validation-record.schema.json`。

这些文件被逐字节复制，没有修改 `$id`、`$ref`、字段或语义。
`benchmarks/mathlib-style/manifests/schemas/MANIFEST.json` 保存来自原始
`MANIFEST_v0.3.0.json` 的 byte count 和 SHA-256。

结构检查验证：

- 文件集合恰好为上述 11 个；
- 每个文件 byte count 和 SHA-256 与原 manifest 一致；
- JSON 可解析；
- 每个 root schema 声明 Draft 2020-12；
- schema ID 唯一；
- 所有本地 `$ref` 文件和 JSON Pointer 均可解析；
- 使用到的 schema keyword 形状有效。

此外，使用标准 `jsonschema` 4.25.1 Draft 2020-12 validator 对全部 11 个 schemas
执行 metaschema 检查，并用原 artifact 的 12 个 schema-validation examples 完成
实例验证；12 个样例全部通过各自的 public-case、private-gold、
private-provenance、prediction 或 validation-record schema。

因此，“schemas 无法恢复”不再是 blocker。

## 6. Version identities

### Evaluation environment

- Mathlib release：`v4.30.0`
- Mathlib commit：`c5ea00351c28e24afc9f0f84379aa41082b1188f`
- Lean toolchain：`leanprover/lean4:v4.30.0`
- Environment ID：`MATHLIB-4.30.0`

### Policy snapshot

- Snapshot ID：`MATHLIB-POLICY-2026-08-13`
- Repository：`leanprover-community/leanprover-community.github.io`
- Commit：`7b967eb1aaab674bd6aead708d42c4a83e2aca05`

### Historical case source environment

当前尚未建立。现有 fixtures 是 synthetic smoke data，不是 mined historical
cases。未来每个 historical case 必须单独记录 base/merge commit、toolchain、
license、porting changes、provenance 和 content hashes。

这三个版本身份不得合并。

## 7. Validation

从仓库根目录运行：

```bash
python3 benchmarks/mathlib-style/scripts/check_distillation.py
python3 benchmarks/mathlib-style/scripts/check_benchmark.py
git diff --check
```

验证覆盖：

- 正式目录和所需文件存在；
- 75 个 rule IDs 唯一；
- rule strength、finding priority 和 task union 未漂移；
- Manual 和 Taxonomy 精确覆盖规则；
- registries 内部引用有效；
- six-index partition 精确覆盖 75 条规则；
- Markdown 本地链接有效；
- 11 个 schemas 的 provenance、hash、结构和本地 references 有效；
- 10 个 evidence anchors 的 commit、path、blob SHA 和 line range 有效；
- fixture metadata 有效；
- held-out 目录没有 answer-key-looking 文件；
- Lean fixtures 通过 forbidden-construct guard；
- 固定 Mathlib checkout 为指定 commit；
- Lean 为 v4.30.0；
- 3 个 fixtures、4 个 Lean 文件编译通过且无 unexpected warning。

smoke harness 仍不是 full benchmark harness。它尚未执行完整 style linter、
axiom baseline/observed/delta、case-specific warning allow-list、
statement/specification preservation 和 task scoring。

## 8. Repository isolation

当前分支为 `experiment/efg-review-baseline`，跟踪
`fork/experiment/efg-review-baseline`，工作树原本已包含大量 EFG 改动。

Phase 1 的修改范围仅为：

- 根 `AGENTS.md` 的短入口；
- 新 `docs/research/mathlib-style/`；
- 新 `benchmarks/mathlib-style/`；
- 验证后移除旧的未跟踪 `mathlib-style-distillation/`。

没有修改、格式化、清理、stage 或 commit 既有 EFG Lean 源码、EFG 文档、
EFG scripts 或 `EFG_Formalization_Exercises.lean`。没有执行 reset、restore、
checkout、clean 或 stash，也没有 push 或创建 PR。

## 9. 后续工作

Phase 2 首要任务是 Manual adversarial audit，而不是立即制造大量正式 cases：

1. 为每条规则查找 supporting evidence；
2. 主动查找 counterexamples；
3. 分类例外和反例；
4. 审计规则 strength、scope 和 qualification；
5. 只提出修订建议，不直接改 normative Manual。

之后才进入 Manual revision、full harness 和 16-case pilot：

- PAIR 6；
- DETECT 4；
- REPAIR 3；
- LOCATE 3。

在这些后续工作完成前，不应声称 Mathlib Style Benchmark 已完成或发布，也不能用
当前 smoke fixtures 得出模型能力结论。
