# EvE sidecar for EconCSLib

> **Status: `stage5a-dev003-executed-evidence-validated-sol-not-authorized`.
> Stage 1 smoke 002 is
> closed at score `1.0`; the public Entry Game direct/transport pair and its 12
> mutations pass Stage 2; the Stage 3 Codex review record verifies at `1.0`.
> Stage 4 completed and re-audited all 12 Luna development cells: direct-route
> run success is static `1/2`, fixed `2/2`, evolved `2/2`; transport-route run
> success is static `1/2`, fixed `0/2`, evolved `0/2`. No rollout changed
> guidance, so this is an implementation/prompt baseline rather than an EvE
> evolution result. Stage 5A DEV-002 executed all 12 cells and 36 Luna sessions;
> one valid local produced/admitted/selected-later chain was observed, but all
> sessions encountered a frozen Python-3.9 checker defect and 25 rollouts lack a
> recorded check chain. DEV-002 is preserved as executed-defective history.
> DEV-003 repaired those defects and completed 12/12 cells and 36/36 Luna
> subscription sessions with mandatory checker evidence in every rollout.
> Three of four evolved cells produced, admitted, and later selected guidance;
> the fourth produced and admitted guidance without a later selection. Four
> pre-reservation preflights failed closed on formal-state drift without
> starting a model or consuming a cell; successor snapshot/quiescence behavior
> must be repaired before separately authorized Sol work.
> Codex review is AI review, not independent human
> review, and none of this is a hidden benchmark, causal condition result,
> formal EvE-effect result, or general model-capability claim.**

## 总体技术路线（v3.6，权威入口）

本节是 EconCSLib EVE 研究计划的**唯一技术路线入口**。后续关于研究目标、
证明路线、实验设计、模型顺序、阶段门槛和任务扩展的决定，都应更新在本节，
而不是另建一份平行路线文档。

文档职责严格区分如下：

- 本 README：长期技术路线、实验原则和阶段顺序；
- [`READINESS.md`](READINESS.md)：当前可运行状态、实时阻塞项和安全边界；
- `*/case.json`：单个任务的冻结规范、受保护资产和确定性评分合同；
- `*/run-manifest.json`：一次实验计划与执行事实，不承载长期路线；
- Lean 源码：声明、证明和保持性质的最高权威；
- [`efg-preservation-matrix.md`](../../docs/design/efg-preservation-matrix.md)：
  EFG 关系强度和已证明保持范围的审查索引。

若本 README 与 Lean 或 EFG governance 冲突，以 Lean 和 governance 为准，
并修订本 README。任何路线更新都必须同时说明变更原因、受影响阶段以及是否
使已有实验失去可比性。

### 0. Proposal 对齐：研究问题、价值与产出

#### 总目标

本项目研究如何把大模型生成、形式化证书、确定性验证和人类审查组合成一条
可复现的算法博弈论自动形式化流程。中心假设不是“大模型能写出足够多的 Lean
代码”，而是：

> **显式的 refinement certificate、假设桥梁和结论运输，能够减少大模型
> 自动形式化中的语义漂移，并使错误接受变得可测量、可定位、可审查。**

Proposal 应围绕以下研究问题组织：

- **RQ1：自动形式化的现状与阻碍。** 大模型在哪些环节已经能帮助生成证明，
  又主要受制于语义建模、抽象选择、定理检索、Lean API 漂移、长程证明构造、
  错误接受、评测泄漏、成本和可复现性中的哪些因素？
- **RQ2：为什么选择算法博弈论。** 该领域同时包含算法、策略空间、信息结构、
  概率、均衡、福利和机制性质，许多结论对建模细节高度敏感，适合检验“代码
  通过编译但数学对象或结论不忠实”的核心风险。
- **RQ3：证书能否改善生成与过滤。** 与只有编译反馈的基线相比，直接路线、
  transport 路线以及两者配对，是否降低 semantic false acceptance，并提高
  错误定位与人工审查效率？
- **RQ4：EvE guidance 是否有效。** 在模型、预算和任务固定时，evolved guidance
  相比 static/fixed guidance 是否提高确定性通过率或降低修复成本？
- **RQ5：结论是否跨模型成立。** Luna 上形成的结果能否在冻结协议下由 Sol
  等条件复现，而不是把底层模型能力误认为 EvE 或证书的效果？
- **RQ6：能否形成可复用规约流程。** 这些任务、证书和评审规则能否沉淀为
  理论教材到 Lean 4 的标准模板，而不是只解决七道 EFG 习题？

算法博弈论的形式化价值分为三层：

1. **社会与软件可靠性。** 拍卖、匹配、平台机制、资源分配和多主体决策可能
   影响真实参与者；实现、边界条件或机制性质的错误可能造成分配和激励偏差。
2. **形式化方法价值。** 该领域迫使系统同时处理依赖行动类型、信息集、机会
   行动、无限/有限历史、策略偏离、概率分布和效用，是连接数学规约与算法实现
   的高密度测试场。
3. **可迁移经验。** source fidelity、refinement、simulation、assumption bridge
   和 conclusion transport 的方法可以迁移到经济模型、协议、编译器和其他
   具有多层语义表示的领域。

Proposal 需要建立一个**可核查的真实错误案例集**来支撑第一层价值。案例必须
有公开的一手来源、明确的软件或机制、错误影响、修复记录以及“形式化本可检查
哪一条性质”的分析；不可用没有版本、复现或来源的轶事代替。案例集是独立的
背景/案例研究工作流，不得与 EVE 的模型能力实验混为一组数据。

#### Proposal 元素到实现工作流的映射

| Proposal 元素 | 在本项目中的准确含义 | 主要产物 | 是否为近期核心 |
| --- | --- | --- | --- |
| 驱动：EvE | EvE 优化 solver candidate 与 guidance；候选模型实际生成 Lean 修改 | Hydra overlay、candidate、lineage、run manifest | 是 |
| 过滤：refinement | 生成并机器检查 relation、hypothesis bridge 和 conclusion transport，而非仅做文本后处理 | certificate、deterministic evaluator、mutations | 是 |
| 其他 simulation | 复用 EconCSLib 已证明关系；借鉴 CompCert 式 simulation/preservation 的义务分解 | relation capability 与 preservation tests | 是，但按任务选择 |
| 自动知识图谱 | 为 theorem/relation 检索提供可选 retrieval 层，不成为数学接受 oracle | 可追踪检索结果与消融实验 | 后置 |
| Mathlib PR 与规范 | 学习声明粒度、命名、依赖、style 和 review finding；不能把接受过的 PR 自动当数学 Gold | review corpus、style/checklist | 支撑项 |
| Review agent | 对已通过 hard gates 的候选给出结构化 findings 和人工升级建议 | findings、mutation recall、review time | 是，但无最终否决/接受权 |
| Human reviewer | 判断 source fidelity、任务价值和 hard gate 未覆盖的语义问题 | 独立审查记录 | 是 |
| Lean 4 到 C++ | 独立的下游 verified extraction/code generation 研究，必须另有语义保持链 | compiler/codegen certificate | 非近期核心 |
| 教材规约化模板 | 从 source lock 到任务、证明路线、证书、评估和审查的标准流程 | 模板、示例和 checklist | Bonus |

这里的“过滤”不是只用 refinement proof 淘汰输出：编译、边界、受保护声明、
assumption delta、负例和 mutation 仍是 hard gates；refinement certificate 解决的
是跨表示运输的语义义务。类似 CompCert 的 simulation proof 是设计这些义务的
重要参照，但本项目只能声称 Lean 中实际建立并由目标定理消费的保持性质。

#### 预期研究产出

- 一套算法博弈论自动形式化任务与确定性 evaluator；
- direct/transport/paired 三类形式化包及 refinement certificate 规范；
- Luna 开发、Luna 冻结实验与 Sol 复制形成的可复现实验记录；
- semantic mutations、错误分类和人机审查数据；
- 经迁移与审查的 EFG 小型 Lean 语料及可复用 relation/theorem；
- Bonus：理论教材章节到 Lean 4 的规约化模板和示例；
- 独立背景产物：算法博弈论软件/机制错误的可核查案例集。

#### Bonus：理论教材到 Lean 4 的规约化流程

该模板在核心实验稳定后再固化，但每个公开任务现在就应尽量保留所需证据：

1. **Source record**：记录版本、章节/题号、合法引用位置、来源哈希和解释者；
2. **Natural-language specification**：把对象、假设、量词、结论和边界条件写成
   可审查的规范，不直接从 OCR 跳到 Lean；
3. **Vocabulary alignment**：把教材术语对齐到 EconCSLib/Mathlib 声明，并记录
   没有现成对象时的新定义理由；
4. **Route selection**：选择 direct、transport 或 paired，声明选择依据和预期
   preservation obligations；
5. **Lean task skeleton**：冻结 import、namespace、允许编辑区、目标声明和
   assumption budget；
6. **Certificate plan**：对 transport 路线逐项列出 relation、假设桥梁、一般
   定理应用和结论运输；
7. **Gold and mutations**：由独立过程建立人工审查的参考证明和针对性错误候选；
8. **Deterministic evaluation**：检查编译、声明、依赖、假设、证书和负例；
9. **Human source-fidelity review**：由 reviewer 回到教材语义，而不是只看 Lean
   文件是否通过；
10. **Upstreaming**：按 Mathlib/EconCSLib 规范重构命名、粒度、文档和复用边界，
    同时保留原实验 artifact，避免为合并而改写历史结果。

### 1. 核心定位

EconCSLib EVE 计划不是单纯的 Lean 代码生成器，而是一个：

> **面向博弈论自动形式化的、证书驱动的生成与审查实验系统。**

核心研究问题是：机器可检查的表示关系、假设桥梁和结论运输，能否降低
自动形式化中的语义漂移和错误接受。

需要区分两个名称：

- **EvE upstream**：Scaling Group 的候选解与 guidance 协同演化框架；
- **EconCSLib EVE program**：本仓库中的任务、证书、评估、审查和实验计划。

本仓库不重新实现 EvE 的调度器、模型 adapter 或 lineage 数据库。EvE 从
独立、固定的 upstream checkout 运行；本仓库只保存 Hydra overlay、公开 seed、
不可变上下文、确定性 evaluator、测试和实验记录。

### 2. 数学核心：两条证明路线

同一个习题允许两条独立证明路线。它们互相校验，但普通任务不强制同时完成。

#### 路线 A：贴近题意的直接证明

在与教材或问题陈述最接近的 `ExerciseModel` 上定义玩家、状态、行动、信息、
机会行动、终止和收益，并通过枚举、计算、归纳或具体构造直接证明目标。

这条路线用于：

- 提供最容易人工审查的语义基线；
- 测量模型的具体数学推理和 Lean 构造能力；
- 为抽象运输路线提供独立回归；
- 防止一般定理或 adapter 掩盖错误建模。

#### 路线 B：一般定理与 refinement certificate

把习题编码为已有一般定理使用的抽象对象，显式证明习题假设能够建立一般定理
假设，并把一般定理的结论运输回习题结论：

```text
Exercise assumptions
        │ hypothesis bridge
        ▼
General theorem assumptions
        │ existing theorem
        ▼
Abstract conclusion
        │ conclusion transport
        ▼
Exercise conclusion
```

`refinement certificate` 在这里是广义术语；实际关系应选择数学上最强但真实
成立的一种，例如严格同构、信息精化、compiler preservation、realization、
simulation、weak/stuttering simulation 或 coupling。任务精化与博弈内部的
`InformationRefinement` 必须在 schema 中使用不同标签。

#### 形式化任务包

接受对象不是固定要求两个模型的笛卡尔积，而是带路线标签的和类型：

```text
FormalizationPackage =
    DirectPackage
  | TransportPackage
  | PairedPackage

DirectPackage =
  SourceLock + TaskSpec + ExerciseModel + DirectProof

TransportPackage =
  SourceLock + TaskSpec + ExerciseEncoding + CanonicalModel
  + RelationCertificate + HypothesisBridge
  + GeneralTheoremApplication + ConclusionTransport

PairedPackage =
  DirectPackage + TransportPackage + AgreementEvidence
```

只有专门比较两条路线的研究任务才要求 `PairedPackage`。配对实验中，两条路线
应使用同一个 source lock 和数学目标，但在独立 solver workspace 中运行，
避免一条路线泄露另一条路线的答案。

### 3. refinement certificate 的最低证明义务

仅证明“两个对象之间存在某种 relation”不足以运输定理。任务必须根据目标
定理显式声明并验证所需的保持范围：

- histories、endpoints 和 action occurrences；
- 合法行动及依赖 action fiber；
- private/public observation 与 decision information；
- chance-kernel pushforward、realization 或 coupling；
- termination、fuel、continuation roots 和 lawful subgames；
- 目标、终局收益、路径事件或结果分布；
- 策略映射、profile update square 和单边偏离覆盖；
- 使用一般定理所需的全部额外假设；
- 抽象结论到原习题结论的最终运输。

均衡结论尤其不能只凭路径或收益保持推出。Nash、SPE、行为/混合策略结论必须
具有相应的偏离覆盖、根语义和策略空间证明。不得把 endpoint forgetting、
macro/micro serialization 或信息变细错误标记为严格同构。

关系注册不另建一套平行自然语言真相源。未来的机器可读 registry 只记录 Lean
声明锚点、能力标签、明确缺失项、适用 theorem family、文档版本和源哈希；
保持性质仍由 Lean 和 preservation matrix 决定。

### 4. 系统边界

技术架构固定为：

```text
Source lock / TaskSpec
          │
          ▼
Pinned EvE upstream + EconCSLib Hydra overlay
          │
          ▼
Isolated solver workspace (normally Candidate.lean only)
          │
          ▼
External deterministic evaluator
          │
          ├── score.yaml       # EvE 最小标量接口
          └── evaluation.json  # 完整门槛与诊断证据
          │
          ▼
Optional LLM/human review and research analysis
```

不在近期路线内另建：Kubernetes、消息队列、Web dashboard、大型向量数据库、
第二套根级 `Eve/` 目录或另一套模型调度器。所有 sidecar 资产继续放在
`experiments/eve/`，运行产物继续放在 `.runtime/`。

### 5. 接受规则

数学接受以确定性 hard gates 为主，不能由 LLM 软分数补偿。最低 hard gates
包括：

1. 固定 Lean toolchain、Mathlib commit、EconCSLib baseline 和 EvE commit；
2. 精确 edit boundary 和受保护资产哈希；
3. 无 `sorry`、`admit`、新增 axiom/constant 或 trusted/native 绕过；
4. 冻结目标声明的精确类型与声明集合；
5. 记录并验证 assumption delta；
6. 按任务路线验证直接证明或完整 certificate chain；
7. 编译、警告、风格和依赖边界；
8. 正例通过，预声明的负例和 mutation 被拒绝；
9. evaluator 自身在运行前后保持不变；
10. 需要来源解释时，保留独立人工 source-fidelity 记录。

当前 EvE 优化评分继续使用确定性的二值语义：全部硬门通过为 `1.0`，任何硬门
失败为 `0.0`。详细错误分类写入 `evaluation.json`。LLM reviewer 可以产生
findings、修复建议或 `HUMAN_REVIEW_REQUIRED`，但不能单独把候选判为数学接受。
软 rubric 只用于人工审查排序和代码质量研究。

### 6. 四类实验必须分开

#### 6.1 工程 smoke

验证 checkout、Hydra loader、Codex、hook、workspace、evaluator、日志和清理。
工程 smoke 成功不代表模型能力、EvE 增益或 benchmark readiness。

#### 6.2 guidance 实验

在同一模型、任务、seed、reasoning effort、turn limit、timeout、工具、网络和
attempt budget 下比较：

1. `static/no-specialized-guidance`；
2. `fixed-initial-guidance`；
3. `EvE-evolved-guidance`。

static/no-optimizer 语义、fixed-guidance 路径和 paired RNG 必须从固定 upstream
源码与实际 Hydra loader 验证，禁止猜测配置字段。不同条件不得共享 resume、
population、cache、日志、guidance 或运行目录。

#### 6.3 证明路线实验

对同一数学目标分别构造 direct 和 transport 任务，比较：

- deterministic success / `correct@k`；
- 编译与修复轮数；
- certificate 完整性；
- 人工审查时间和修改量；
- 对 API 漂移的敏感度；
- 失败类型，而不只比较代码行数。

#### 6.4 审查实验

固定 Gold 和 mutation candidates，不让生成器参与，分别测量编译器、固定规则、
certificate checker、反例检查、LLM reviewer 和人工 reviewer 的：

- semantic false acceptance rate；
- false rejection rate；
- mutation recall；
- finding 定位准确率；
- 人工审查时间。

不得使用同一个 LLM 同时生成、决定 Gold 并充当最终 acceptance oracle。

### 7. 模型路线：Luna 探路，Sol 复现

模型计划固定为以下顺序：

1. **Luna 工程阶段**：使用显式模型名 `gpt-5.6-luna`，先以 `low`
   reasoning 完成模型访问 smoke 和低成本调试；该阶段允许修改任务与提示，
   因而数据不用于正式结论。
2. **协议冻结**：冻结任务、提示、guidance、evaluator、budget、seed、失败策略、
   工具和统计方法。正式 reasoning effort 在此时预声明；`medium` 是当前首选，
   但必须由开发任务测量后决定。
3. **Luna 正式实验**：在全新运行根上重新执行冻结协议，不能复用开发阶段状态。
4. **Sol 等条件复现**：使用显式模型名 `gpt-5.6-sol`，完整重跑相同条件；
   不允许只让 Sol 跑 evolved 条件。

分析顺序是先比较每个模型内部的 static/fixed/evolved，再比较 Luna 与 Sol。
这样才能区分 guidance 演化效果和底层模型能力。通过 ChatGPT subscription 的
实际模型权限、额度和 seed 行为必须由无凭证泄露的本机 smoke 验证；API 标价
不作为订阅实验成本的替代证据。

### 8. 分阶段路线与退出门槛

#### Stage 0：sidecar scaffold（当前已完成）

- 固定 EvE v0.2.0 身份和四层 overlay；
- Stage 0 Mathlib-style plumbing smoke；
- Stage 1a EFG reachability/history micro-pilot；
- 单文件边界、确定性 evaluator、正反 fixture 和结构测试。

退出含义仅为 `scaffold-ready`，不等于已部署或已执行。

#### Stage 1：本机部署和 Luna manual smoke（已完成）

- 准备独立、固定 EvE checkout 并执行 `uv sync --locked`；
- 运行全部本地 fixture、`--check` 和 `--dry-run`；
- 保持已验证的 Codex hook trust；Luna 模型访问已由单回合 smoke 验证；
- 已执行冻结的 Luna config-migration prompt，EFG driver 和 run manifest 已写入
  精确 `gpt-5.6-luna` 配置；经后续明确授权，`case.json` 的两个迁移后保护哈希
  已同步；
- `EVE-STAGE1-LUNA-EFG-MANUAL-SMOKE-001` v1.0.0 已按冻结协议消费：仅一次
  `EvE-evolved-guidance` execution、一次 Luna session、5/10 turns、零 resume、
  零 retry，流水线状态为 completed，deterministic score 为 `0.0`，且没有形成新的
  guidance；候选只在最后一个依赖类型等式证明处编译失败，不构成任务求解成功；
- 审计发现 solver 在隔离 HOME 中通过 `elan` 自检时看不到宿主已安装的 Lean
  4.30.0，因而错误进入离线下载/锁等待。launcher 现把身份核验后的直接 Lean
  toolchain 路径注入隔离环境，并以 accepted fixture 验证可编译且不创建隔离
  `.elan`；完整 45 项测试通过；
- `EVE-STAGE1-LUNA-EFG-MANUAL-SMOKE-002` v1.0.0 已作为全新、单次 follow-up
  执行并审计：一次 EvE execution、一次 Luna session、5/10 turns、零 resume/retry，
  score `1.0`，15 项确定性 gate 全过；没有复用 001 candidate/session/run root，
  toolchain 下载/锁问题未复发；
- 002 的最终 candidate 和 evaluator 已在全新临时目录独立重跑并产生相同哈希。
  审查由 Codex 完成并标记为 AI review，不冒充独立人工审查；
- 两次 smoke 均未修改 guidance，也没有产生 optimizer candidate，因此 Stage 1
  只完成工程闭环，不支持 EvE guidance evolution 的效果结论。

退出标准是 runner/evaluator/日志闭环真实工作；002 已满足该标准，Stage 1 关闭。

#### Stage 2：首个 direct/transport 配对 micro-task（已完成）

- 从 Entry Game 或现有 reachability 任务中抽取一个小而精确的数学目标；
- direct 与 transport 分成两个独立任务和 solver workspace；
- transport 任务要求完整 hypothesis bridge 与 conclusion transport；
- 先建立 8--10 个针对性 mutation，不追求任务数量。

已实现 Entry Game 同题双路径：direct accepted fixture、transport accepted fixture
和 pair agreement 均为 `1.0`；transport 路径包含完整的编码、payoff preservation、
strict-hypothesis bridge、`RefinementCertificate`、一般定理实例化与结论回运。
公开 mutation corpus 共 12 项，全部按预声明 failure gate 被拒绝。因此退出标准已满足。

#### Stage 3：公开 review benchmark micro（已完成）

- 固定 Gold/mutation 候选；
- 分离生成评估与审查评估；
- 统计 semantic false acceptance 和 false rejection；
- LLM reviewer 只提供结构化 finding，不控制 hard acceptance。

Codex 已按冻结 rubric 审查两个 accepted candidate 与 12 个 mutation：accepted
均无 P1/P2 阻断项，mutation rejection recall 为 `12/12`，blocking false accept 为
`0`。一致性 verifier 得分 `1.0`。该记录明确标为 `codex-ai-review`，不是独立人工
review，也不替代 deterministic evaluator 的数学接受权。

#### Stage 4：Luna 三条件公开开发实验（已执行并由 Codex 审查）

- 已从固定 upstream 源码与真实 Hydra loader 建立 static、fixed、evolved 语义；
- 已预声明两个独立 EvE sampler seed：`1729`、`2718`；
- 12 个 fresh run roots 已完整执行 static、fixed、evolved；
- 命令、退出码、seed audit、候选/日志哈希、模型/CLI/环境身份均已保留。

冻结协议为 `stage4_protocol.json`：两条证明路线 × 三个条件 × 两个 seed，共
12 个 fresh cells；每个 cell 两次迭代、单 worker、最多 6 turns/rollout、禁止
resume/import/retry。`run_seeded_eve.py` 在 factory 构造后且第一次采样前分别播种
solver population、optimizer population 和 worker-selection RNG，不修改 pinned
upstream。Codex/provider adapter 不暴露模型 seed，因此模型采样仍不可控；这一限制
记录在每次 seed audit 中，绝不把 paired EvE seed 描述为端到端确定性。

`stage4_review/audit.json` 是本批的收口记录。机器审计重新执行了全部 24 个候选的
确定性 evaluator，并逐项比对 status、score、failure codes、gates 和 axioms；结果
完全一致。Codex 又审阅了代表 10 个通过实例的 6 份唯一源码：五份 direct 源码均
使用具体四 profile 穷举；唯一通过的 transport 源码完整构造 certificate、调用两
个一般定理，并把 encoded equality 运输回具体 profile。没有 blocking false accept。

本批只能作为实施性基线：四个 evolved cell 的八个 rollout 全部未修改 guidance，
`optimizer_candidates_produced = 0`，因此不存在“新 guidance 在后续迭代被选中”的
观测。fixed/evolved 与 static 的差异也不能作因果解释，因为 provider model RNG
不可控且每组仅 `n=2`。

#### Stage 5A：DEV-002 历史缺陷与 DEV-003 执行归档

`EVE-STAGE5-LUNA-ENTRY-GAME-GUIDANCE-LIVENESS-DEV-001` 经执行前审查发现四项
阻断缺陷，已在零 run root、零模型 session 的状态下整版作废；其 checkpoint、hash、
原 Codex AI review 和四项 finding 保留在 Git 与
`stage5a_invalidated_protocols.json`。新协议
`EVE-STAGE5-LUNA-ENTRY-GAME-GUIDANCE-LIVENESS-DEV-002` 与 Stage 4 DEV-002
完全独立；Stage 4 的 protocol、audit、population、guidance、candidate、session 和
run root 均不复用，也不回写历史结果。`stage5a_protocol.json` 及 detached SHA-256
冻结两条 Entry Game 路线、三个条件、两个 EvE sampler seed 和 12-cell 顺序。

`stage5a_lean_environment.json` 冻结从公共 compilation 入口递归得到的 109 个本地
Lean 模块、三个 Lake/toolchain 元数据文件和 manifest 中全部依赖 checkout revision；
预检重新计算完整 closure，要求每个外部 checkout 位于精确 commit 且 tracked-clean，
执行前还必须构建冻结入口。协议专属 SQLite ledger 在任何模型子进程前以事务方式
预约唯一的下一个 ordinal，拒绝重复、跳号、乱序和前序未终结的 cell。

同一路线三个条件共享字节完全相同的 prompt bundle。两类编辑面不再矛盾：solver
候选面严格为 `solver/Candidate.lean`；只有在已记录真实 Lean 失败后，才可编辑
`guidance/docs/learned.md`，其他路径均禁止。immutable checker 为每次真实检查记录
连续 hash chain、checker/candidate/guidance tree hash、exit status 和输出 hash。
只有某个有效失败事件的 guidance snapshot 与最终 produced tree 不同，才能证明
保留的 guidance change 发生在失败之后并归类为 failure-derived；失败计数或自然语言
声明均不充分。static 从空 guidance 开始且不保留变化；fixed 与 evolved 从相同
route guidance 开始，fixed 不保留变化，只有 evolved 允许 upstream 对真实 changed
tree 产生 optimizer candidate。

固定 upstream 生命周期证明 candidate 在第 `i` 轮加入 population 后，最早只能在
第 `i+1` 轮成为 working optimizer；理论最少需要两轮。本协议预声明三轮、单
worker、每轮一次 solver session、8-turn budget、900 秒 timeout、零
retry/resume/import，每 cell 最多 3 sessions，全矩阵最多 36 sessions。这样第 1
或第 2 轮产生的 candidate 都有后续选择机会；第 3 轮才产生则必须报告
`PRODUCED_WITHOUT_LATER_OPPORTUNITY`，不得误报 selected。

`run_stage5a_eve.py` 只在 pinned 方法调用前后增加 id/hash/iteration 观测，不改变
采样、candidate 构造、population admission 或 Phase 3 评分。`audit_stage5a.py`
再以只读方式连接 attempt ledger 与 optimizer lineage database，校验完整 ordinal
历史和 Lean-check chain，并区分：failure-before-change、guidance tree changed、
candidate produced、entered population、以及 exact candidate id/hash 在更大
iteration 被 selected。upstream database 没有保存 parent iteration 或每次 working
selection，因此这些缺失 join 由 sidecar JSONL 补充；自然语言日志不能单独证明
failure-derived 或 selected later。provider model RNG 仍不可控并写入每次
launch/seed/audit 记录。

transport 的公共不可变模板固定全部十项 checkpoint：最终 concrete theorem 精确
签名、action/profile encoder、payoff preservation、严格假设 bridge、Nash/SPE
preservation、完整 `RefinementCertificate`、显式消费 certificate projections、调用
固定一般定理、encoded equality reflection/完整具体 action 分类、以及回运到原题
concrete profile 类型和精确声明。

经用户明确授权，DEV-002 的 12 个 cell 和 36 个 Luna session 已按冻结顺序一次性
完成，零 retry/resume/import，12 份 machine audit 重跑后逐字节一致。共生产并入池
4 个 failure-derived guidance candidate；direct/2718/evolved 第 1 轮 candidate 在
第 2、3 轮被严格后续选择，形成一条真实的本地 liveness chain。

但 post-run transcript review 发现 immutable checker 使用 `datetime.UTC`，而隔离
solver Python 为 3.9.6。36/36 session 均至少触发一次异常，共 91 次失败调用；只有
11 个 session 通过运行时兼容绕行留下 57 条有效链，25 个 rollout 的 check list 为空。
现有 auditor 会验证存在的链，却允许空链，因此 DEV-002 不是干净协议执行。原始
evaluator 得分与 ordinal 6 的有效链作为历史观测保留，但不能形成条件比较、因果、
模型能力或 Sol replication 结论。`stage5a_review/dev002-audit.json` 是执行前 AI 审查，
`stage5a_review/dev002-execution-audit.json` 是执行后收口记录。下一步只能准备新的
协议身份并另行审查；未经单独授权不得执行或启动 Sol。

后继协议 `EVE-STAGE5-LUNA-ENTRY-GAME-GUIDANCE-LIVENESS-DEV-003` 版本
`3.0.0`、SHA-256
`4c407b3e654d4e38f6f35b48e924863b5a9ef72c1e6b9569996e86f00105ad49`
现已冻结为 `FROZEN_NOT_YET_EXECUTED`。它使用全新的 config/overlay、RNG domain、
run-root parent 和 SQLite ledger，不读取或写入 DEV-002 执行状态。两个 immutable
checker entrypoint 字节一致，使用 Python 3.9.6 可用的 `datetime.timezone.utc`；wrapper
与 auditor 对缺失、空、畸形、hash/runtime/output 不一致或 final-candidate 不匹配的
check evidence 全部 fail closed，且未验证的 failure flag 不能伪造 liveness。

DEV-003 将 Lean source 固定到 canonical fork 的 clean commit
`b490317186ef435670c2eeb16050a214cdbf9fe5`，从 Git object 重算 109-file closure，禁止
把当前混合用户工作区作为执行源。独立 fresh clone 构建冻结入口并通过 exact-runtime
safe preflight；该 preflight 在正式 root/ledger 预约前，用 `/usr/bin/python3` 3.9.6、
同一 checker 和 Lean 工具链记录真实非零 Lean exit 与 stdout/stderr/event hashes。
12/12 `--check`、12/12 `--dry-run` 与完整 EVE suite 均通过。冻结文件继续保留
`FROZEN_NOT_YET_EXECUTED` 这一不可变 launch input；实际执行事实另记于
`stage5a_review/dev003-execution-audit.json`。

经用户明确授权，DEV-003 已用 ChatGPT subscription 认证按冻结顺序完成 12/12 cell、
36/36 Luna session；12 条 ledger 记录均 exit code 0，零 retry/resume/import，36 个
rollout 均保存必需 checker evidence，12 份 machine audit 重跑逐字节一致。raw candidate
passes 为 direct static/fixed/evolved 均 `0/6`，transport 为 `0/6`、`2/6`、`0/6`。
四个 evolved cell 共生产并入池 9 个 failure-derived guidance candidate；ordinal
3、6、9 各有一个 candidate 在严格后续轮次被选择，ordinal 12 生产并入池 3 个但未
后续选择。

cell 之间共有 4 次 preflight 因 formal-state snapshot 漂移而 fail closed：1 次
`--execute` 和 3 次零模型 `--check`，全部发生在 attempt reservation 与模型访问前，
未产生 retry 或重复 cell。后继或 Sol 协议必须在新 identity 中修复 mutable SQLite
sidecar 的 snapshot/quiescence 行为。当前结果是干净 checker 与本地 liveness mechanism
观测，不是因果 EvE effect、模型能力、benchmark/evaluation 完成或 Sol replication
结果；Sol 尚未执行或授权。

#### Stage 6：七题 EFG 任务扩展

当前 `EFG_Formalization_Exercises.lean` 是七题历史工作稿和未来 Gold 候选来源，
不是已验证 benchmark。它必须先迁移到当前 EFG API，并按题目、路线和声明边界
拆分。扩展顺序暂定：

1. Entry Game；
2. Three-Pile Misère Nim；
3. Information-Set Refinement；
4. Poker Game；
5. Entrant with Incomplete Information；
6. Absent-Minded Driver；
7. Chomp。

每个任务先形成公开小切片，再决定是否扩大证明目标。不得把 15k 行工作稿整体
暴露给 solver 或作为单一 Gold fixture。

#### Stage 7：正式/私有研究（保持禁用）

只有在独立人工审核、Linux evidence、物理 evaluator 隔离、数据 split、泄漏
测试、预算冻结和多 seed 设计全部完成后，才允许私有 holdout 或正式 Phase 4/5
实验。知识图谱、训练数据、PR 自动 mutation 和更广的 simulation 生成均后置。

### 9. 数据、来源与隔离

- 教材 PDF、扫描件、OCR 内容和不可再分发原文不得进入仓库；任务保存合法改写、
  文献位置、来源哈希和人工解释记录。
- 公开任务可以包含公开 seed 和公开 mutation；真实 holdout 的 Gold、evaluator、
  provenance 和 answer-revealing score intermediate 不得挂载给 worker。
- 私有子模块本身不构成隔离。正式评估需要独立账户、容器或等价边界，采用
  单向 candidate transfer 和清洗后的 score return。
- 输入上下文、模型输出和执行轨迹在保存前必须去除 credential、环境变量、
  私有路径和受版权限制的原文。
- 任何运行都记录 task/prompt/rubric 版本、模型角色、reasoning effort、Codex
  CLI、EvE/Lean/Mathlib/EconCSLib 身份、requested/effective seed、budget、命令、
  退出码和 artifact hashes。

### 10. 当前实现基线（2026-08-21）

- Stage 1 的历史 45 项测试在 002 收口时为 45 pass、0 skip；Stage 2--4 新增了
  paired evaluator、mutation/review verifier、六种 Hydra condition 和 seed wrapper
  覆盖；2026-08-21 使用固定 checkout 的最新完整结果为 53 pass、0 skip（111.661s），
  包括 Luna 配置、清单、访问证据、真实
  Hydra 合成、隔离 HOME 下的 accepted Lean 编译，以及全部 EFG/Stage 0 evaluator
  正负例；
- EFG micro-pilot solver prompt `EVE-EFG-SOLVER-PROMPT-001` v1.0.0 已冻结；
  它是 Luna/Sol 共用的模型中立提示合同，已在 manual smoke 001 中执行一次，结果
  为 `EXECUTED_SCORE_ZERO`；
- 一份用户提供的手工 candidate 已归档为
  `.runtime/manual-stage1-efg-reachability-001`，完整 deterministic evaluator 得分
  `1.0`；其模型来源和 Codex/EvE 执行轨迹未验证，因此不构成 Luna、EvE 或
  benchmark 结论；
- operator prompt `EVE-STAGE1-LUNA-PREFLIGHT-001` v1.0.0 已冻结，用于只读验证
  checkout、依赖、Hydra、launcher 和 Codex authentication；它禁止模型调用和
  `--execute`；对应 preflight 已达到 `READY_FOR_SEPARATE_MODEL_ACCESS_SMOKE`；
- operator prompt `EVE-STAGE1-LUNA-ACCESS-SMOKE-001` v1.0.0 保持冻结。首次预条件
  检查因外层 sandbox 拒绝用户级 uv cache 而阻塞，模型尝试为 `0`，该记录已保留；
  修复检查假阴性后，其唯一一次 `gpt-5.6-luna`、low effort、只读、ephemeral
  模型回合以 `LUNA_ACCESS_SMOKE_PASSED` 完成，精确返回 `EVE_LUNA_ACCESS_OK`，
  无工具事件，预算使用 `1/1`。未发生 retry、fallback、EvE 执行或配置迁移；
- operator prompt `EVE-STAGE1-LUNA-CONFIG-MIGRATION-001` v1.0.0 已冻结并哈希锚定。
  它已在不调用模型的条件下写入 scoped Luna driver、EFG 顶层 config、未运行的
  run manifest 和结构测试；首次完整验证发现 `case.json` 的两个旧保护哈希后，
  经用户明确追加授权仅同步这两个锚点，完整验证通过，执行报告为
  `LUNA_CONFIG_MIGRATION_READY`。该报告不授权 manual smoke；
- operator prompt `EVE-STAGE1-LUNA-EFG-MANUAL-SMOKE-001` v1.0.0 已冻结并哈希
  锚定，状态为 `EXECUTED_COMPLETED`。它授权的唯一一次
  `EvE-evolved-guidance` execution 已完成：一次 Codex/Luna session、5/10 turns、
  零 resume/retry、score `0.0`、无 guidance 更新。报告、candidate、evaluation 和
  post-run audit 均已保留；该结果只证明本地流水线闭环，不证明模型能力；
- 运行后审计确认 candidate 的前六个声明正确，最后一个定理在 `Sigma.ext_iff`
  产生 `HEq` 而目标需要 `Eq` 处失败；同时确认隔离 solver 的 Lean 自检因 toolchain
  发现方式进入离线下载/锁等待。sidecar 已改为注入经版本核验的 Lean 4.30.0 直接
  binary 目录，并增加隔离 HOME 回归；修复过程没有模型或 EvE 调用；
- operator prompt `EVE-STAGE1-LUNA-EFG-MANUAL-SMOKE-002` v1.0.0 已冻结并哈希
  锚定，状态为 `EXECUTED_COMPLETED`。它没有复用 001 的 prompt budget、candidate、
  session、resume/import state 或运行根；最终 score `1.0`，15/15 gates 通过；
- 002 post-run audit 状态为 `MANUAL_SMOKE_002_AUDITED_STAGE1_COMPLETE`。审查者为
  Codex AI，不是独立人类；candidate 与 evaluator 的独立重跑哈希匹配；
- 本机独立 checkout `/Users/lyuyuwei/Documents/eve-v0.2.0` 已固定到 EvE v0.2.0
  tag object `74e59e4...` 和 commit `50b2399...`，`uv sync --locked`、真实 Hydra
  loader、`--check`、`--dry-run` 与 launcher accepted fixture 均已通过；
- 该 checkout 已在 Codex CLI `0.148.0-alpha.21` 中完成项目级信任与四类 hook
  trust；EvE 自带校验返回 `project_trusted=True`、`missing_events=[]`，相关 upstream
  hook/isolation/sandbox 测试 26 项通过，sidecar `--check` 现会只读报告
  `codex hook trust: available`；确认过程中未提交普通提示词或触发模型调用；
- macOS 上 uv editable `.pth` 的 hidden flag 会被 Python 3.13 跳过；sidecar 的
  probe 与 execute 现显式使用 identity-verified `checkout/src` 作为 `PYTHONPATH`，
  同时继续使用 `uv --offline --frozen --no-sync`。probe/trust 使用一次性可写
  `UV_CACHE_DIR`，未来 execute 使用 run root 内的独立 cache，避免受限外层 sandbox
  把用户级 cache 访问拒绝误报为 hook trust/locked environment 不可用。upstream
  源码和 venv 元数据未改；
- Stage 1 EFG smoke 路径恰好执行过两次 `--execute` / EvE runner / Luna Lean
  solver session，另有一次更早的只读 Luna access smoke；Stage 0 execution 未运行；
- Entry Game direct/transport 的 deterministic route score 与 pair score 均为 `1.0`，
  12 个 mutation 均被拒绝；Stage 3 Codex review verifier 为 `1.0`，且没有冒充
  independent human review；
- static/fixed/evolved 语义已由固定 EvE v0.2.0 源码哈希和真实 loader 验证；
  sidecar 为 upstream 原本无配置入口的三个 EvE `random.Random` 流增加了运行前
  domain-separated 播种。模型 RNG 仍不可配置；
- `EVE-STAGE4-LUNA-ENTRY-GAME-DEV-002` 的 12-cell、24-session 上限和零 retry
  协议已完整执行；12 个唯一 cell、24 个候选、100 agent turns、零 resume/import
  经机器审计一致，原 DEV-001 的一次 Hydra 启动失败发生在模型调用前并已整版排除；
- Stage 4 run-level 结果为 direct `static 1/2, fixed 2/2, evolved 2/2`，transport
  `static 1/2, fixed 0/2, evolved 0/2`；失败候选为 compile `9`、route discipline
  `3`、target contract `2`。所有 evolved rollout 均未更新 guidance，optimizer
  candidate 总数为 `0`；
- Stage 5A DEV-001 因四项执行门缺陷在零 run、零 session 状态下整版作废；独立
  DEV-002 的 12 个 cell、36 个 Luna session 已按冻结顺序完成，生产并入池 4 个
  failure-derived guidance candidate，其中 1 个在严格后续轮次被选择；但 36/36
  session 均触发 Python-3.9 `datetime.UTC` checker 缺陷，25 个 rollout 没有记录
  check chain，因此 DEV-002 作为 executed-but-unclean 历史证据保留，不授权 Sol；
- Stage 5A DEV-003 以全新 identity 修复 Python 3.9 checker、exact-runtime safe
  preflight、required-evidence fail-closed、no-false-liveness、fresh ledger/order 与
  clean committed Lean boundary；12 cell、36 Luna session 已完成，9 个 candidate
  生产并入池，3 个在严格后续轮次被选择，全部 rollout 有必需 checker evidence；
  4 次 pre-reservation guard activation 未预约 attempt 或启动模型，Sol 未授权；
- 当前 EFG driver/manifest 已记录显式 `gpt-5.6-luna`、low effort 和
  Codex-default/unpinned verbosity；清单保留 001 score-zero、002 score-one 和
  comparative conditions 的历史 not-run 事实。两次都没有 guidance 更新。冻结 case
  protection 与完整测试均已通过。Stage 0 legacy driver 仍保持 `gpt-5.4-mini`；
- `EFG_Formalization_Exercises.lean` 包含七题工作稿，但在当前 API 上不能通过
  Lean，已观察到 `IsDecision`、`RepresentedInfo`、finite hypothesis fields 和
  strategy carrier 等系统性迁移错误；它当前不是 Gold；
- Stage 4 运行前只提交/冻结 `experiments/eve/` sidecar，不纳入工作树中其他用户
  修改；即使提交，该公开 answer-visible development baseline 也不是 benchmark release。

### 11. 路线更新规则

后续每次修改本技术路线时：

1. 更新本 README，不创建平行总体方案；
2. 在变更处记录日期、原因和受影响 stage；
3. 若改变任务、模型、effort、budget、evaluator、seed 或统计方法，则增加新的
   protocol version，不覆盖既有实验定义；
4. 同步更新 `READINESS.md` 的实时 blocker，但不把计划写进 readiness；
5. 已执行 run-manifest 保持事实记录，不为适配新叙事而回写；
6. 关系强度或 API 结论的变化必须先由 Lean、preservation matrix 和 governance
   支持；微实验得分不能授权核心 API 变化。

#### 变更记录

- **2026-08-22 · v3.6**：经明确授权用 ChatGPT subscription 认证执行并收口
  Stage 5A DEV-003 全部 12-cell、36-session Luna matrix。12 个 attempt 按冻结顺序
  exit 0，零 retry/resume/import，36 个 rollout 均有必需 checker evidence；12 份
  machine audit 重跑逐字节一致。raw passes 为 direct 三条件均 `0/6`，transport
  `0/6, 2/6, 0/6`。四个 evolved cell 共生产并入池 9 个 candidate，其中 ordinal
  3、6、9 各有 1 个在后续轮次被选择，ordinal 12 未选择。另记录 4 次发生在预约与
  模型访问前的 formal-state guard activation；它们未消耗 cell，但后继/Sol identity
  必须修复 SQLite sidecar snapshot/quiescence。未执行或授权 Sol，不形成因果、能力、
  benchmark 或 evaluation-complete 结论。
- **2026-08-21 · v3.5**：冻结并审查独立 Stage 5A DEV-003（protocol v3.0.0）。两份
  checker 兼容 exact Python 3.9.6；safe preflight 在正式状态前以相同 runtime、checker、
  Lean toolchain 与 clean committed source 记录真实失败事件；wrapper/auditor 对空、
  畸形、漂移或候选不匹配证据 fail closed，未验证的 failure 不能建立 liveness。新的
  roots/ledger/order/RNG domain 不继承 DEV-002。独立 fresh clone 验证 109-file closure
  并构建入口；12 项 DEV-003 定向测试、87 项完整 EVE 测试（2 项逐项记录跳过）、12 个
  check 与 12 个 dry-run 通过。零 DEV-003 模型调用、session、quota、正式 root/ledger；
  状态停在 `FROZEN_NOT_YET_EXECUTED`，执行与 Sol 均需另行授权。
- **2026-08-21 · v3.4**：经明确授权一次性执行 Stage 5A DEV-002 全部 12-cell、
  36-session Luna 矩阵，零 retry/resume/import，账本与 12 份 machine audit 均通过
  且重跑逐字节一致。候选得分为 direct 三条件均 `0/6`，transport static `3/6`、
  fixed `2/6`、evolved `1/6`；4 个 failure-derived guidance candidate 生产并入池，
  direct/2718/evolved 的 iteration-1 candidate 在 iteration 2、3 被后续选择。
  post-run review 同时发现冻结 checker 的 `datetime.UTC` 与 solver Python 3.9.6
  不兼容：36/36 session、91 次调用受影响，25 个 rollout 无记录链；现有 auditor
  允许空链。DEV-002 因此按已执行但不干净的协议收口，不重试、不授权 Sol，修复需
  新 protocol identity、fresh roots/ledger、新 review 与另行执行授权。
- **2026-08-21 · v3.3**：执行前审查否决 Stage 5A DEV-001：它未冻结传递 Lean
  依赖、未强制单次/顺序启动、不能证明失败先于 guidance change，且 prompt 编辑面
  自相矛盾。保留 001 checkpoint、detached hash 和旧 review，在零 run root、零模型
  session 下整版作废。以 DEV-002 冻结 109 个本地 Lean import closure、Lake/toolchain
  元数据和 dependency commits；新增模型访问前 SQLite ordinal reservation、连续
  Lean-check/guidance hash chain、failure-before-change 判定和明确双编辑面。21 项定向
  回归、75 项完整 EVE 测试（2 项按设计跳过）、Stage 4 本地证据复核、12 个 check 与
  12 个 dry-run 均通过；未创建 DEV-002 runtime root/ledger，未运行 `--execute`，未
  产生 Luna session、新 guidance 或 Sol replication。
- **2026-08-21 · v3.2**：新增并冻结独立 Stage 5A Luna guidance-liveness 公开开发
  协议 `EVE-STAGE5-LUNA-ENTRY-GAME-GUIDANCE-LIVENESS-DEV-001`。从 pinned EvE
  v0.2.0 源码建立完整 phase/iteration 证据，确认 produced 与 later-selected 的最小
  两轮顺序，并为协议预声明三轮。两条路线分别使用跨 condition 字节相同的 prompt；
  公共 Lean checker 记录真实 exit status 和 candidate/output hashes；只读 sidecar
  lineage 把 changed、produced、population admission 和严格后续 working selection
  分开验证。transport 固定十项 certificate/transport checkpoints。协议、输入和
  detached hash 已冻结，审查身份仅为 `codex-ai-review`。没有运行 `--execute`，没有
  Stage 5A Luna session，没有新 guidance produced/selected，也没有开始 Sol 复制。
- **2026-08-21 · v3.1**：完整执行并收口 `DEV-002` Stage 4 Luna 公开开发矩阵。
  第一次 `DEV-001` 启动在任何模型 session 前暴露 Hydra primary-config 解析缺陷，
  已记录、整版作废并修复为显式 absolute-config CLI；真实 CLI 零模型预检和 53 项
  回归通过后，以新协议一次性执行 12 个 cell。机器审计重新评测全部 24 个候选，
  无重复、resume/import、结果漂移或 false accept。Codex AI 源码审查确认两条路线
  的通过候选满足各自证明原则。四个 evolved cell 没有产生 guidance/optimizer，
  所以本批仅关闭实施性 Stage 4，不形成 EvE-evolution 或因果效果结论；下一阶段先
  以新协议激活并观测 guidance produced/selected，再复制到 Sol。
- **2026-08-20 · v2.3**：收口 fresh manual smoke 002。唯一一次 post-repair
  execution 以 one Luna session、5/10 turns、零 resume/retry 完成，candidate
  score `1.0` 且 15/15 deterministic gates 通过；旧 001 运行树保持不变，elan
  下载/锁问题未复发。最终 candidate 与 evaluator 在独立临时目录重跑得到相同
  哈希。新增 Codex AI post-run audit、同步 operator/run/case records，并明确两次
  smoke 都没有 guidance 修改或 optimizer candidate，所以只关闭 Stage 1 工程
  门槛，不形成 EvE 增益结论或独立人工审查证据。Stage 2 public direct/transport
  开发由用户授权开始。
- **2026-08-20 · v2.2**：核验并固化 manual smoke 001 的唯一一次实际运行：
  one iteration、one Luna session、5/10 turns、零 resume/retry、流水线 completed、
  score `0.0`、无 guidance 更新。候选的编译失败定位到最后一个 `Sigma` 依赖等式
  证明；solver 自检还暴露了隔离 HOME 下 `elan` 无法发现宿主 Lean 4.30.0、继而
  尝试离线下载和等待锁的问题。sidecar 现注入经身份核验的直接 toolchain 路径，
  并新增不创建隔离 `.elan` 的编译回归；45 项测试、EFG `--check`/`--dry-run` 和
  artifact 哈希一致性通过。001 的预算保持耗尽，另行生成并冻结不复用任何旧状态
  的 `EVE-STAGE1-LUNA-EFG-MANUAL-SMOKE-002`；修复与冻结过程没有模型调用。
- **2026-08-20 · v2.1**：修正 config-migration operator manifest 的事实记录为
  `EXECUTED_READY` / `LUNA_CONFIG_MIGRATION_READY`，并生成、哈希冻结首个单条件
  Luna EFG manual-smoke 提示词。新协议固定 `EvE-evolved-guidance`、一次
  `--execute`、一次 Codex session、最多 10 turns、零 retry/resume/repair，明确
  区分流水线完成与 candidate 的 0/1 分数，并保留 static/fixed/paired RNG、默认
  verbosity 和正式实验 blocker。完整 42 项测试、真实 Hydra 合成、EFG `--check`
  与 `--dry-run` 通过；提示词仍为 `FROZEN_NOT_RUN`，本次没有模型调用或 EvE 执行。
- **2026-08-20 · v2.0**：在用户明确追加授权后，仅更新 `case.json` 中 EFG 顶层
  配置与 run manifest 的两个迁移后保护哈希，消除首次验证发现的合同冲突。完整
  41 项 sidecar 测试、两份 manifest JSON、真实 Hydra 合成、EFG `--check` 与
  `--dry-run`、固定 artifact 哈希、checkout/hooks 身份和仓库边界全部通过。迁移
  状态推进到 `LUNA_CONFIG_MIGRATION_READY`，但仍是 configured-not-run；下一步
  单条件 manual smoke 需要另行授权，static/fixed/paired RNG 与 verbosity blocker
  均未解除。整个迁移没有调用模型、`codex exec`、EvE runner 或 Lean solver。
- **2026-08-20 · v1.9 validation note**：执行冻结的 Luna config-migration
  prompt，新增 scoped `codex_luna_offline`，仅让 EFG 选择显式
  `gpt-5.6-luna`，并把未运行清单迁移到 schema v1.1.0。JSON、真实 Hydra 合成、
  sidecar `--check`/`--dry-run` 与新结构测试通过；完整 41 项测试有 12 failure，
  均因冻结 `case.json` 仍锚定 EFG 顶层配置和 run manifest 的迁移前哈希。该文件
  不在本提示授权范围内，故状态为 `FAILED_VALIDATION`，路线版本不提升，manual
  smoke 继续禁止。该迁移未调用模型、`codex exec`、EvE runner 或 Lean solver。
- **2026-08-20 · v1.9**：生成并冻结
  `EVE-STAGE1-LUNA-CONFIG-MIGRATION-001` v1.0.0。迁移方案不覆盖共享 legacy
  driver，而是为 EFG 新增 `codex_luna_offline`，固定显式 `gpt-5.6-luna` 与 low
  effort，并要求 run manifest 保留 not-run 事实和全部 static/fixed/paired RNG
  blocker。由于固定 EvE v0.2.0 adapter 不暴露 `model_verbosity`，提示词要求如实
  记录 Codex-default/unpinned，不能把单条件 engineering smoke 提升为可比较实验。
  新增提示词哈希与无执行授权结构测试，共 39 项；生成阶段未调用模型或 EvE。
- **2026-08-20 · v1.8**：确认 `EVE-STAGE1-LUNA-ACCESS-SMOKE-001` 的首次阻塞是
  外层 sandbox 拒绝用户级 uv cache 造成的检查假阴性；保留零模型尝试的阻塞记录，
  并令 sidecar 的 dependency/hook probe 使用一次性 cache、execute 使用 per-run
  cache。随后核验同一冻结协议唯一一次 Luna 调用通过，JSONL 仅含一个精确 agent
  message、无工具事件，哈希、checkout commit 与 hook payload 均匹配，预算已用
  `1/1`。38 项 sidecar 测试通过；下一门槛改为模型/config manifest 迁移，未运行
  EvE 或 Lean solver。
- **2026-08-20 · v1.7**：生成并冻结 `EVE-STAGE1-LUNA-ACCESS-SMOKE-001`
  v1.0.0，将下一门槛收敛为一次显式 `gpt-5.6-luna` access smoke。协议使用只读
  sandbox、ephemeral session、JSONL 证据、low effort 和严格的一回合/不重试预算，
  并禁止工具、fallback、EvE、Lean solver 与配置迁移。新增 manifest/hash 结构测试；
  提示词生成阶段未产生模型调用。
- **2026-08-20 · v1.6**：审查固定 EvE v0.2.0 的 hook 生成器与 workspace guard，
  生成并哈希固定 checkout 的 repo hook，完成 Codex 项目级及 `pre_tool_use`、
  `post_tool_use`、`session_start`、`user_prompt_submit` 四类信任。新增无凭证、离线、
  只读的 sidecar trust probe；36 项 sidecar 测试和 26 项 upstream hook/isolation/
  sandbox 测试通过。Stage 1 下一门槛收敛为单独授权的 Luna access smoke；仍未运行
  EvE runner、`--execute` 或模型调用。
- **2026-08-20 · v1.5**：经用户授权下载并验证独立 EvE v0.2.0 checkout，完成
  `uv sync --locked`。修复 macOS/Python 3.13 跳过 hidden editable `.pth` 导致的
  dependency probe 假阴性，使 probe/execute 都从已验证 checkout 显式加载源码。
  35 项测试、真实 Hydra loader、`--check`、`--dry-run` 和 accepted fixture 全部
  通过；Stage 1 状态推进到 `READY_FOR_SEPARATE_MODEL_ACCESS_SMOKE`，仍无模型调用。
- **2026-08-20 · v1.4**：归档首份手工 EFG candidate、恢复冻结 seed 并取得
  deterministic score `1.0`；由于没有可信模型 provenance，仅记录为 harness/
  proof acceptance。新增 `EVE-STAGE1-LUNA-PREFLIGHT-001` v1.0.0 及哈希 manifest，
  把 Stage 1 的 checkout/config/auth 预检与后续模型访问 smoke 分离。影响 Stage 1
  运行顺序，但没有产生模型比较数据。
- **2026-08-20 · v1.3**：生成并冻结 Stage 1 EFG micro-pilot solver prompt
  `EVE-EFG-SOLVER-PROMPT-001` v1.0.0，补足目标、成功条件、证据边界、验证和停止
  规则。影响 Stage 1 的未来运行协议；由于尚无模型运行，不使任何已有结果失去
  可比性。Luna 与 Sol 必须共用该版本，除非登记新的 prompt/protocol version。
- **2026-08-20 · v1.2**：纳入 proposal 的研究现状、算法博弈论价值、真实错误
  案例、驱动/过滤/观测、知识图谱、Mathlib review、Lean-to-C++ 和教材模板问题；
  将其分为核心研究、支撑工作和后置/Bonus。影响研究表述及 Stage 3/6/7 的产出，
  不改变既有任务、evaluator 或实验协议，已有运行的可比性不受影响。
- **2026-08-20 · v1.1**：把两条证明路线、certificate obligations、Luna→Sol
  模型顺序和 Stage 0--7 计划收敛到本 README，建立单一技术路线入口。

---

以下章节保留 sidecar 的具体运行、身份验证、安全命令和清理说明。

[EvE](https://github.com/scaling-group/eve) is Scaling Group's framework for
co-evolving solver candidates and agent guidance. EconCSLib remains a Lean/Lake
project. EvE runs from a separate pinned checkout, while this directory stores
only the EconCSLib-specific Hydra overlays, public seeds, immutable worker
contexts, deterministic evaluators, safe launcher, tests, and readiness
records.

## Immutable upstream identity

`UPSTREAM.lock.json` pins the annotated tag `v0.2.0` (tag object
`74e59e489bd918f109ffe2a9ccdc8beb4a977e01`) and its peeled commit
`50b2399258ab08b6225a87cd05bded9701caa23d`. The launcher rejects any checkout
whose origin, commit, tag object, LICENSE hash, or NOTICE hash differs.

EvE is Apache-2.0 licensed. This repository does not vendor or redistribute its
source. Keep upstream `LICENSE` and `NOTICE` in the external checkout. If a
future distribution includes EvE or a derivative, review and satisfy the
Apache-2.0 license and NOTICE preservation requirements.

Prepare an external checkout at a narrow, explicit path:

```bash
git clone --branch v0.2.0 https://github.com/scaling-group/eve.git /absolute/path/eve-v0.2.0
git -C /absolute/path/eve-v0.2.0 rev-parse HEAD
git -C /absolute/path/eve-v0.2.0 checkout 50b2399258ab08b6225a87cd05bded9701caa23d
cd /absolute/path/eve-v0.2.0
uv sync --locked
```

The pin requires Python `>=3.11,<3.15`; upstream's `.python-version` is `3.13`.
Upstream requires `uv` but declares no minimum version. It uses Codex as its
default agent backend and declares no minimum Codex version; its hook-trust
procedure applies to Codex `>=0.130.0`.

## Architecture and boundary

The launcher passes `experiments/eve/configs/eve` through Hydra's
`--config-dir`; it never copies config files into the upstream checkout. At
execution time it creates an ignored per-run overlay and adds a hash-recorded
immutable copy of the normative English manual. The worker receives the public
seed plus immutable instructions. The formal evaluator remains external.

The launcher has exactly two hard-coded experiment choices:

- `mathlib-style-smoke` selects the existing `mathlib_style_smoke` plumbing
  smoke and remains the CLI default for backward compatibility;
- `efg-reachability-micro` explicitly selects the new
  `efg_reachability_micro` Stage 1a usability task.

There is no argument for an arbitrary Hydra config, case, seed, evaluator,
reference, gold, or private path. The explicit `--eve-checkout` argument is
only the separately verified official EvE v0.2.0 checkout.

The four EvE configuration layers are:

- application: the local public seed and the exact solver edit boundary;
- evaluation: one deterministic shell step and fallback score;
- optimizer: initial general guidance, immutable context, prompt, and scalar
  Elo adapter;
- experiment: safe runtime, one-iteration loop, offline Codex driver, and local
  CSV logging composition.

For both experiments the solver edit boundary is exactly `Candidate.lean`;
`editable.folders` is empty. The evaluator, config, immutable context, prompt,
seed baseline, accepted fixture, tests, protected hashes, and scoring logic
are outside that boundary. EvE compares the complete solver snapshot to the
baseline before evaluation. Each local evaluator repeats the boundary check
and snapshots protected evaluator assets around Lean elaboration.

Guidance evolution is EvE's separate optimizer surface. Initial guidance is
general and must not encode the fixture's answer. A solver boundary violation
receives `score: 0.0` and skips evaluation; boundary repair attempts are set to
zero.

## Public Stage 0 smoke

The smoke is derived from the public synthetic
`benchmarks/mathlib-style/fixtures/repair/rep_dollar_syntax/` fixture. It is
copied into `smoke/seed/` so the original fixture remains untouched. The worker
snapshot contains no reference repair or evaluator.

The deterministic evaluator:

1. verifies the exact candidate boundary and frozen seed hash;
2. verifies `leanprover/lean4:v4.30.0` and Mathlib commit
   `c5ea00351c28e24afc9f0f84379aa41082b1188f`;
3. invokes the repository's existing strict static Lean guard;
4. rejects additional trusted bypass forms;
5. compiles with the pinned Mathlib standard linter set;
6. rejects every warning (the allow-list is empty) and requires FMT-008 to be
   resolved;
7. proves a declaration/value preservation contract and checks an empty target
   axiom delta;
8. runs Mathlib's pinned `lint-style` text/Unicode validator;
9. verifies protected evaluator assets did not change.

The audited directory/hash/boundary/process/score primitives are shared with
the EFG evaluator through `scripts/evaluator_common.py`; target-specific
mathematical checks remain separate.

EvE `v0.2.0` accepts a YAML PyTree at `logs/evaluate/score.yaml`. This smoke
writes exactly a numeric `score` plus a `summary`. Higher is better: `1.0`
means every deterministic gate passed; evaluation failure and boundary failure
both use the worst score `0.0`. There is no random or LLM-judge component.

## Public Stage 1a EFG reachability micro-pilot

`efg_reachability_micro` is independent of the Mathlib-style smoke. It tests
only usability of the existing EFG minimal StructuralCore on one public local
task. Investigation found that the current facade already exposes
`Arena.reachable_iff_nonempty_history`, `Arena.History.toReachable`, and
`Arena.HistoryFrom`. The pilot therefore asks a solver to discover and use the
existing interface; it does not duplicate a theorem or modify EFG source.

The seed imports only:

```lean
import EconCSLib.GameTheory.ExtensiveGame.Interface.StructuralCore
```

It fixes a two-action diamond whose histories merge at one endpoint and asks
for exact local declarations proving:

- `A.Reachable start finish ↔ Nonempty (A.History start finish)` in both
  logical directions;
- each concrete branch forgets to reachability;
- the two reachability proofs are equal by proof irrelevance;
- the concrete histories and `HistoryFrom` occurrences remain different even
  though their endpoints agree.

The seed is intentionally incomplete without using `sorry`. The accepted
fixture exists only under `efg_reachability_micro/expected/` for evaluator
self-tests and is never copied into a model solver workspace. The evaluator
requires the exact task prefix and sole import, rejects placeholders,
axioms/constants, spoofing, native/trusted bypasses, warnings, type drift, and
invalid diamond claims, prints every target's axioms, and runs the EFG
API-growth and governance checks. Any hard failure writes the same worst score
as a boundary failure:

```yaml
score: 0.0
summary: "one or more deterministic EFG micro-pilot gates failed"
```

A complete deterministic pass writes `score: 1.0`. Scoring does not compare
candidate text to the accepted fixture and uses no LLM judge. Success would
show only that one solver run satisfied this local task under this harness. It
would not prove model capability, that EvE improved the solver, or that the EFG
minimal core should be changed.

## Safe commands

Use one explicit external checkout path in every command:

```bash
python3 experiments/eve/scripts/run.py \
  --eve-checkout /absolute/path/eve-v0.2.0 \
  --check

python3 experiments/eve/scripts/run.py \
  --eve-checkout /absolute/path/eve-v0.2.0 \
  --dry-run

python3 experiments/eve/scripts/run.py \
  --eve-checkout /absolute/path/eve-v0.2.0 \
  --evaluate-fixture accepted
```

The EFG micro-pilot must be named explicitly for every action:

```bash
python3 experiments/eve/scripts/run.py \
  --eve-checkout /absolute/path/eve-v0.2.0 \
  --experiment efg-reachability-micro \
  --check

python3 experiments/eve/scripts/run.py \
  --eve-checkout /absolute/path/eve-v0.2.0 \
  --experiment efg-reachability-micro \
  --dry-run

python3 experiments/eve/scripts/run.py \
  --eve-checkout /absolute/path/eve-v0.2.0 \
  --experiment efg-reachability-micro \
  --evaluate-fixture accepted
```

`--check` is offline. It validates identity, local tools, assets, and the actual
pinned Hydra loader if the locked upstream environment is already synced.
`--dry-run` is a wrapper-owned preview because EvE `v0.2.0` has no native
dry-run flag; it never imports the runner, starts Codex, or makes a network
request. `--evaluate-fixture` runs only the local deterministic evaluator.

The existing Stage 0 execution spelling remains unchanged. It launches EvE
and may consume model quota; that Stage 0 execution has not run:

```bash
python3 experiments/eve/scripts/run.py \
  --eve-checkout /absolute/path/eve-v0.2.0 \
  --execute
```

The new EFG path additionally requires both the explicit experiment and a
model-quota acknowledgement. This is the execution spelling used once by the
consumed manual-smoke-001 protocol:

```bash
python3 experiments/eve/scripts/run.py \
  --eve-checkout /absolute/path/eve-v0.2.0 \
  --experiment efg-reachability-micro \
  --acknowledge-model-quota \
  --execute
```

Do not run that command again outside an active frozen operator prompt.
Manual-smoke-001 consumed its single authorized attempt and completed with
deterministic score `0.0`. Manual-smoke-002 then consumed its separate fresh
attempt and completed with score `1.0`; both prompts are permanently exhausted.
A separate earlier read-only, ephemeral `codex exec` access smoke also completed
and exhausted its one-turn budget. Do not rerun either manual-smoke command.

Stage 4 仅允许 `stage4_protocol.json` 中的 task/condition/seed 组合。例如一个
不调用模型的预览和一个显式授权的 cell 写法是：

```bash
python3 experiments/eve/scripts/run.py \
  --eve-checkout /absolute/path/eve-v0.2.0 \
  --experiment entry-game-direct \
  --condition static \
  --experiment-seed 1729 \
  --dry-run

python3 experiments/eve/scripts/run.py \
  --eve-checkout /absolute/path/eve-v0.2.0 \
  --experiment entry-game-direct \
  --condition static \
  --experiment-seed 1729 \
  --acknowledge-model-quota \
  --execute
```

launcher 不接受协议外 seed、condition、任意 config 或第二次 attempt。每个
execution 使用 fresh ignored run root，并写 `stage4-launch.json` 与
`eve-sampler-seed.json`。Stage 4 matrix 由当前用户授权执行；执行记录仍需逐 cell
审计，不因某一 cell 成功而自动补跑失败 cell。

Stage 5A DEV-003 的安全入口还要求一个 detached-at-frozen-commit、tracked-clean 的
Lean checkout。下面两个命令均为零模型调用；`--check` 会实际构建冻结入口并在一次性
workspace 中运行 deliberately-failing exact-runtime checker，`--dry-run` 只预览：

```bash
python3 experiments/eve/scripts/run_stage5a_dev003.py \
  --eve-checkout /absolute/path/eve-v0.2.0 \
  --lean-checkout /absolute/path/clean-econcslib-at-b490317 \
  --experiment entry-game-direct \
  --protocol-id EVE-STAGE5-LUNA-ENTRY-GAME-GUIDANCE-LIVENESS-DEV-003 \
  --condition static \
  --experiment-seed 1729 \
  --check

python3 experiments/eve/scripts/run_stage5a_dev003.py \
  --eve-checkout /absolute/path/eve-v0.2.0 \
  --lean-checkout /absolute/path/clean-econcslib-at-b490317 \
  --experiment entry-game-direct \
  --protocol-id EVE-STAGE5-LUNA-ENTRY-GAME-GUIDANCE-LIVENESS-DEV-003 \
  --condition static \
  --experiment-seed 1729 \
  --dry-run
```

不得把当前 mixed worktree 传给 `--lean-checkout`。上述 check/dry-run 仍可用于
只读验证，但 DEV-003 的 12 个 attempt 已全部消耗；不得再次附加
`--acknowledge-model-quota --execute`，也不得 retry/resume/import。

Execution remains offline at the dependency and web-search layers
(`uv --offline --frozen --no-sync`, Codex web search disabled), but Codex agent
calls can still consume the authentication and quota configured by the user.

## Codex authentication and hook trust

Do not paste or print tokens, API keys, environment variables, or Codex
credentials. Configure Codex authentication through its normal interactive
flow. The sidecar discards `codex login status` output and reports only
authentication availability; it never inspects or prints credential values.

EvE uses repository hooks for workspace protection. The sidecar never grants
hook trust; it only checks the resulting state without printing credentials.
On this machine the procedure below was completed for the identity-verified
`/Users/lyuyuwei/Documents/eve-v0.2.0` checkout on 2026-08-20. Repeat it only
for a new checkout path or changed hook payload before `--execute`:

```bash
cd /absolute/path/eve-v0.2.0
uv run python -m scaling_evolve.providers.agent.codex_hooks
codex -C /absolute/path/eve-v0.2.0
```

Inside Codex, open `/hooks`, review the hooks, explicitly trust them, then exit.
EvE's runner will hard-fail if the required project and hook trust is absent.
The current four required events are `pre_tool_use`, `post_tool_use`,
`session_start`, and `user_prompt_submit`; the latest local verification found
no missing event.

The model-access gate is frozen as
`operator_prompts/STAGE1_LUNA_ACCESS_SMOKE.md` and has completed with
`LUNA_ACCESS_SMOKE_PASSED`. Its only authorized `gpt-5.6-luna` turn is spent;
do not run it again. The frozen
`operator_prompts/STAGE1_LUNA_CONFIG_MIGRATION.md` has written the scoped EFG
driver and run manifest without a model call. After explicit follow-up
authorization updated only the two corresponding frozen case hashes, the
complete validation passed with `LUNA_CONFIG_MIGRATION_READY`.
Manual-smoke-001 completed with score zero; its audited isolated-toolchain
feedback issue was repaired. Manual-smoke-002 then completed with score one and
closed the Stage 1 engineering gate. Both runs left guidance unchanged.

## Stage 4 three-condition protocol (executed and Codex-reviewed)

`stage4_protocol.json` freezes these conditions for both Entry Game routes:

1. `static/no-specialized-guidance`;
2. `fixed-initial-guidance`;
3. `EvE-evolved-guidance`.

它们共享 `gpt-5.6-luna`、low effort、6-turn limit、900 秒 timeout、两次迭代、
单 worker、相同 evaluator/tool/network/attempt budget，并用 `1729`、`2718` 两个
EvE sampler seed 跨条件配对。static 以 runtime 空目录播种 optimizer；fixed 与
evolved 从完全相同的 route guidance tree 起步；fixed/static 的
`produce_optimizer_in_phase2=0`，evolved 为 `1`。真实 Hydra loader 已对两条路线
的全部三种组合验证这些值。

`stage4_upstream_semantics.json` 锁定 upstream commit 和六个相关源码哈希。
upstream 本身会为 population 与 worker builder 创建无参 `random.Random()`，没有
原生 seed 配置；sidecar wrapper 因此在 factory 返回后、initial guidance 和 loop
之前播种三个实例。这个控制范围不包括 Codex/provider model sampling。配置、源码
证据、限制和每次运行 seed audit 必须同时保留，不能只写“seed 已固定”。

两次历史 EFG smoke 均未演化 guidance，不能充当三条件比较。Stage 4 使用全新
Entry Game run roots；12 个 cell 各只有一次 attempt，失败也作为结果保留。正式/
私有 Phase 4/5 material 继续 hard-disabled 并物理断开，本公开开发矩阵不解除其
Linux、独立人工 review、private isolation 或 split blocker。

All 12 DEV-002 cells completed. The independently repeated deterministic audit
matched every archived candidate status, score, failure code, gate, and axiom
record. Run-level outcomes are direct `1/2, 2/2, 2/2` and transport
`1/2, 0/2, 0/2` for static, fixed, and evolved respectively. These are raw
development outcomes at `n=2`, not significance or causal claims. All eight
evolved rollouts left guidance unchanged and produced zero optimizer
candidates; evolved was enabled but inactive.

## Stage 5A guidance-liveness protocols

`stage5a_protocol.json` and `stage5a_protocol.sha256` freeze the independent
protocol `EVE-STAGE5-LUNA-ENTRY-GAME-GUIDANCE-LIVENESS-DEV-002`. Its frozen
status remains the historical launch input `FROZEN_NOT_YET_EXECUTED`; do not
rewrite that file after execution. DEV-001 was
invalidated in full before execution with zero run roots and zero model
sessions; its checkpoint, hash, review, and four blockers remain historical
evidence. The DEV-002 matrix's 12 cells
retain the Entry Game direct/transport scope, three conditions, and seeds
`1729`/`2718`, but use three iterations and a fresh dedicated run-root parent
`experiments/eve/.runtime/stage5a-dev002-runs/`. No Stage 4 run root, population,
guidance candidate, cache, session, resume, or import is a Stage 5 input.

The frozen Lean environment manifest covers the 109-file local transitive import
closure, Lake/toolchain metadata, and exact clean dependency checkout commits;
the entry target must build before launch. A durable protocol-specific SQLite
ledger transactionally reserves the exact next ordinal before model access and
rejects duplicate or reordered cells. The route-local prompt bundle hash is
identical across static, fixed, and evolved, with explicit independent edit
surfaces for `solver/Candidate.lean` and conditional
`guidance/docs/learned.md`.

A common immutable local checker records a contiguous hash chain with checker,
candidate, guidance-tree, exit, and output hashes at every real Lean check. A
candidate is failure-derived only if a valid failed check's guidance snapshot
differs from the produced tree, proving a later retained change. Runtime
observation then records production, admission, and exact later selection. The
post-run auditor opens both the attempt ledger and optimizer lineage storage
read-only. Production without a later selection is reported as such; a
terminal-iteration candidate has no later opportunity; no candidate is
`NO_GUIDANCE_PRODUCED`.

After explicit user authorization, all 12 cells and 36 Luna sessions completed
once in frozen order with fresh roots, no retry/resume/import, and ledger exit
code zero. Re-running the post-run auditor for every root reproduced all 12
machine reports byte-identically. Candidate-level deterministic outcomes were:

| Route | static | fixed | evolved |
|---|---:|---:|---:|
| direct | 0/6 | 0/6 | 0/6 |
| transport | 3/6 | 2/6 | 1/6 |

Four failure-derived guidance candidates were produced and admitted. In the
direct/2718/evolved cell, the iteration-1 candidate was selected in iterations
2 and 3, so that local lineage has status
`GUIDANCE_PRODUCED_AND_SELECTED_LATER`. Direct/1729/evolved produced one
candidate that was not selected later; transport/1729/evolved produced none;
transport/2718/evolved first produced in the terminal iteration.

Post-run transcript review found a blocking defect not rejected by the frozen
preflight or auditor. The solver environment used Python 3.9.6, while the
immutable checker uses `datetime.UTC`. Every one of the 36 sessions triggered
the resulting exception at least once (91 failed invocations). Solvers found a
runtime compatibility workaround in some rollouts, leaving 57 valid chained
events across 11 sessions, but 25 rollouts have empty check evidence. The
auditor validates a chain when present yet permits an empty list. The external
evaluator scores and the valid ordinal-6 lineage remain historical raw
observations, but DEV-002 is not a clean protocol execution and cannot support a
comparative, causal, model-capability, or Sol-replication claim.

The tracked post-execution record is
`stage5a_review/dev002-execution-audit.json`. Preserve all DEV-002 runtime roots
and the attempt ledger. The 12 attempts are consumed and must not be retried.
Any repair requires a new protocol identity, fresh roots and ledger, exact
isolated-runtime checker preflight, fail-closed missing-check evidence, review,
and separate execution authorization.

That repair is frozen as `stage5a_dev003_protocol.json` plus its detached hash,
under identity `EVE-STAGE5-LUNA-ENTRY-GAME-GUIDANCE-LIVENESS-DEV-003` version
`3.0.0`. DEV-003 superseded DEV-002 only as a separate clean-evidence execution;
it does not rewrite, retry, resume, import, or reclassify DEV-002 evidence. Its
status is `FROZEN_NOT_YET_EXECUTED` and its review is
`stage5a_review/dev003-audit.json`.

DEV-003 freezes Python-3.9-compatible byte-identical checkers, exact-runtime
preflight before formal state, mandatory nonempty and final-candidate-matched
evidence, and a post-run auditor that revalidates the clean source/preflight
record as well as every rollout chain. It also freezes a fresh matrix ledger,
run-root parent, RNG domain, and clean canonical Lean source commit. An
independent fresh clone at that commit reproduced the 109-file environment,
built the entry target, and ran the real checker preflight. Every planned cell
passed `--check` and `--dry-run` before execution.

After explicit authorization, all 12 DEV-003 cells and 36 Luna subscription
sessions completed once in frozen order, with no retry/resume/import. Mandatory
checker evidence is present in all 36 rollouts, and all 12 machine reports
replay byte-identically. Raw outcomes are direct `0/6, 0/6, 0/6` and transport
`0/6, 2/6, 0/6` for static, fixed, and evolved. Nine failure-derived guidance
candidates were produced and admitted. Evolved ordinals 3, 6, and 9 each
selected one exact candidate later; ordinal 12 produced three candidates but
selected none later.

Four inter-cell preflights failed closed on formal-state snapshot drift before
reservation or model access. They consumed no attempt or session, but their
SQLite sidecar snapshot/quiescence trigger must be repaired in any successor or
Sol protocol. The tracked result is
`stage5a_review/dev003-execution-audit.json`. It supports clean local checker and
liveness-mechanism observations, not a causal, capability, benchmark,
evaluation-complete, or Sol-replication claim.

Any proposed `Arena`, controlled-carrier, StructuralCore-closure, or
Canonical/Frontend API change discovered later must return to the documented
EFG freeze/governance human decision process. A micro-pilot score never
authorizes such a change, and the draft EFG prompt pack is not evidence that a
Lean theorem exists.

## Artifacts and cleanup

All sidecar-created run roots, solver/evaluation workspaces, logs, populations,
SQLite lineage databases, telemetry, snapshots, caches, temporary evaluator
trees, and copied manuals live below the ignored directory
`experiments/eve/.runtime/`. No generated artifact belongs in the Lean/Lake
tree. The external upstream checkout separately contains its ignored,
`uv`-managed `.venv` and the upstream-generated Codex hook file after the
documented manual hook command.

The Stage 4 and Stage 5A run roots, ledgers, and full machine-audit reports are
local evidence for `stage4_review/audit.json`,
`stage5a_review/dev002-execution-audit.json`, and
`stage5a_review/dev003-execution-audit.json`. Do not clean them until they have
been archived to an approved evidence store; the tracked hashes prove identity
but cannot reconstruct deleted transcripts or candidates. Before any later
cleanup, verify the target exactly:

```bash
find experiments/eve/.runtime -maxdepth 2 -print
```

Only after confirming it contains tool-generated data and the Stage 4 evidence
has been archived, remove that exact directory with `rm -rf --
experiments/eve/.runtime`. It is not versioned. Do not broaden the target or
substitute a home, repository, or workspace root.

## Tests

From the EconCSLib repository root:

```bash
python3 -m unittest discover -s experiments/eve/tests -v
python3 experiments/eve/scripts/audit_stage4.py --no-recheck
python3 experiments/eve/scripts/verify_stage4_review.py --require-local-evidence
python3 experiments/eve/scripts/verify_stage5a_protocol.py
python3 experiments/eve/scripts/verify_stage5a_dev003_protocol.py
python3 -m json.tool experiments/eve/UPSTREAM.lock.json >/dev/null
python3 -m json.tool experiments/eve/smoke/case.json >/dev/null
python3 -m json.tool experiments/eve/efg_reachability_micro/case.json >/dev/null
python3 -m json.tool experiments/eve/efg_reachability_micro/run-manifest.json >/dev/null
```

Repository-level Mathlib-style checks remain authoritative and are listed in
the task's validation record.

## Known limitations

- Exactly two bounded evolved-labelled Stage 1 engineering smokes and 12
  Stage 4 public development cells have run. Stage 4 produced no optimizer
  candidate, so guidance-evolution effectiveness remains untested.
- Stage 5A DEV-001 was invalidated before execution. DEV-002 executed but has a
  blocking checker/auditor defect; its one local liveness chain is historical,
  not a clean comparison. DEV-003 completed with clean mandatory checker
  evidence and three local liveness chains, but the small answer-visible matrix,
  uncontrolled provider sampling, lack of independent human review, and four
  pre-reservation guard activations do not establish a causal comparison or
  authorize Sol.
- Neither public synthetic/local task can support a benchmark,
  model-capability, EvE-improvement, or minimal-core optimization conclusion.
- EvE has no native dry-run at the pin; the sidecar prevents invocation.
- The formal Phase 4/5 pilot and all private custody are intentionally
  disconnected.
- Static/fixed/evolved and EvE-sampler seed semantics are source/loader
  verified. Provider model RNG and verbosity remain unavailable in the pinned
  adapter, so end-to-end deterministic replay is not claimed.
- Physical worker/private-evaluator isolation, randomized evaluation splits,
  budget controls, fair baselines, and multi-seed study design remain future
  work. See `READINESS.md`.
