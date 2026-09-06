# 任务：EFG 一步执行与有限前缀的表示多态可行性研究

> 产品代码只读；允许独立、可删除的 Lean 探针与研究报告。

## 1. 研究目标

严格判断：EconCSLib 的 EFG 概率执行层中，是否存在一个足够小的表示无关内核，使同一份“一步执行／有限前缀”算法可以分别解释为：

1. 可实际求值的有限离散有理数概率或次概率对象；
2. Mathlib 的测度论 `Kernel`。

在这两个后端通过后，再单独判断现有 `EffectiveKernel` 或它的适当扩展能否加入同一接口。这个判断不是初始探针的成功条件。

本任务是可行性研究，不预设重构值得实施，也不预设任何 `noncomputable` 声明必然消失。必须分别验证以下命题，不得把其中一个命题的成立当成另一个命题的证据：

- **G1：共同算法骨架。** 一步执行与有限前缀能否只依赖一组明确、足够小的运算及定律。
- **G2：有限后端可执行。** 同一个泛型算法在有限后端实例化后，能否通过真实求值得到结果。
- **G3：Kernel 后端语义精确。** 同一个泛型算法在 `Kernel` 后端实例化后，能否与现有分析定义证明外延相等。
- **G4：表示之间相容。** 从有限表示到测度／Kernel 的解释映射，能否保持共同运算，并使相应计算图交换。
- **G5：库级收益。** 若 G1–G4 成立，实际能复用哪些声明，能减少多少重复实现、证明或 `noncomputable` 声明。

只有 G1–G4 均有形式化证据时，才可以把已验证的局部范围称为“表示多态实现”。不得由局部探针把结论外推到整个 EFG。G5 必须按逐声明依赖闭包计算，不能从关键词命中数量推断。

## 2. 明确不属于本轮目标的事项

本轮不做以下工作：

- 不修改 `EconCSLib/` 下的任何产品源码；
- 不修改聚合导入、脚本、测试、CI 或治理规则；
- 不把探针模块导入 `EconCSLib.lean` 或任何稳定模块；
- 不替换、删除或重命名现有公开声明；
- 不承诺降低当前 `noncomputable` 声明总数；
- 不试图把无限路径概率律、正则条件分布、积分、任意可测空间上的一般 Kernel 变成有限算法；
- 不把一个现有 `Kernel` 值包进泛型接口后称为“同一算法的两个后端”；
- 不把 `EffectiveKernel` 预先认定为第三个后端；
- 不处理 `Examples/` 中与核心可行性无关的迁移或清理工作。

## 3. 工作区与产物约束

先读取仓库根目录的 `AGENTS.md` 并遵守其全部约束。保留当前工作区已有修改；禁止 `stash`、`checkout`、`reset`、`clean`、提交或推送。

产品源码保持只读。失败的实验、生成文件和临时 Lake 项目全部放在：

```text
/tmp/econcslib-representation-polymorphism-*
```

只有最终通过检查、能够独立复现结论的两个文件可以写入仓库：

```text
docs/research/efg-computability/RepresentationPolymorphismProbe.lean
docs/research/efg-computability/REPRESENTATION_POLYMORPHISM_FEASIBILITY.md
```

如果这些目标文件已经存在，先读取并保留其中仍有效的证据；不要盲目覆盖。若无法在不损害现有内容的前提下更新，报告阻塞原因。

为了让同一文件中的 Kernel 实例直接引用泛型定义，`RepresentationPolymorphismProbe.lean` 作为未被任何库模块导入的研究探针，可以在模块级导入 Mathlib Kernel。这是对研究产物的局部豁免，不是对生产架构的授权。泛型代数和有限后端的声明本身不得引用 `Measure`／`Kernel` 常量；还必须把这两部分原样抽取到 `/tmp` 的 pure-boundary 探针中，仅使用当前纯算法层可用的 imports 单独编译，并在报告中记录命令与结果。

## 4. 先建立动态基线

开始前记录：

```bash
git status --short --branch
python3 scripts/check_efg_computability.py
```

若现有 `.olean` 依赖追踪已被 Lake 验证为新鲜，可以在第一次清点时使用 `--skip-build` 降低成本；最终结论前仍需运行完整检查。开始时还要把受保护产品目录的 diff、状态和内容哈希清单写到 `/tmp`，以便发现“原本已 dirty 的文件又被本任务修改”这种仅看 `git status` 无法识别的情况。至少保护：

```text
EconCSLib/
EconCSLib.lean
scripts/
tests/
.github/
```

提示词编写时的已知基线是：全库约 137 个、主库约 58 个、Examples 约 79 个 `noncomputable` 声明。该数字只是历史参照。以执行时脚本输出为准；数字变化本身不应中止研究，但必须在报告中解释差异。

至少阅读下列现有设计、审计和实现材料；若路径在当前版本中有变化，使用 `rg --files` 定位对应文件并记录映射：

```text
docs/design.md
docs/design/efg-document-authority.md
docs/design/efg-library-computability.md
docs/design/efg-library-computability-declarations.md
docs/design/efg-computability-migration.md
docs/design/efg-semantic-compatibility.md
docs/design/efg-semantic-universes.md
docs/design/efg-public-api.md
docs/design/efg-module-status.md
docs/design/efg-algorithm-implementation-ledger.md
docs/design/efg-algorithm-opportunity-audit.md
docs/design/efg-finite-computation-prompts.md
docs/design/efg-proof-audit.md
scripts/efg_computability_classification.json
docs/research/efg-computability/LibraryFeasibility.lean
```

其中以 `efg-document-authority.md` 判定文档职责；把迁移文档与算法台账中 A19、A20 的当前状态作为基线，不能按旧提示词把已经完成的阶段重新当成待办。若路径在执行时确实变化，才使用 `rg --files` 定位后继文件并记录映射。

### 4.1 保护现有 A19/A20 架构事实

本研究不得把重做已有结果记成收益。至少核对并保护以下事实：

- A19 已建立纯算法 aggregate 与 opt-in analytic semantics 的导入分层；若后续进入生产实施，泛型代数和有限后端必须位于不导入 `Measure`／`Kernel` 的 pure owner，Kernel 实例和交换证明必须位于独立 semantic leaf；本轮单文件研究探针按第 3 节的有限豁免处理；
- A20 已包含高层 profile 编译、有限前缀算法和逐 horizon 分析桥；新探针必须逐项说明相对于这些定义与桥定理新增了什么；
- 本任务只授权研究产物。任何稳定模块、aggregate、公开声明或 API-growth 例外都属于后续实施决策，不能由本提示词自动授权。

还要检查实际存在的相邻实现，尤其是以下主题对应的模块：

```text
EconCSLib/GameTheory/ExtensiveGame/Execution/Discrete/KernelArena.lean
EconCSLib/GameTheory/ExtensiveGame/Execution/Discrete/KernelTrajectory.lean
EconCSLib/GameTheory/ExtensiveGame/Execution/Discrete/HistoryKernel.lean
EconCSLib/GameTheory/ExtensiveGame/Execution/Discrete/EffectivePathLaw.lean
EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/Execution.lean
EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/StatePath.lean
EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/EventPath.lean
EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/HistoryPath.lean
EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/FiniteExecution.lean
EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/EffectivePathLaw.lean
EconCSLib/GameTheory/ExtensiveGame/Simulation/Restart/FiniteExecution.lean
EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Kernel/EffectiveBehavioralProfile.lean
EconCSLib/GameTheory/ExtensiveGame/Simulation/Continuation/Conditioning.lean
```

不要只读文档中的结论。对报告中引用的关键声明，必须回到当前 Lean 源码核对签名、类型类条件、定义体和直接消费者。

## 5. 第一阶段：逐声明静态矩阵

在写泛型接口前，先为主库中脚本当前识别出的每个 `noncomputable` 声明建立一行简表，记录声明、位置、直接根因，并分入 `candidate`、`explicit boundary`、`downstream propagation` 或 `unknown`。然后只对 Gate A–E 所需的候选声明建立深表。深表至少包含：

| 字段 | 要求 |
|---|---|
| 声明 | 完整限定名与源码位置 |
| 当前签名 | 输入、输出和关键类型类条件 |
| 不可计算根因 | 直接根因与传递根因分开记录 |
| 所需概率运算 | 如确定性、复合、零、分段、乘积、映射、积分、条件分布 |
| 候选有限语义 | 概率、次概率、有限支持、是否要求有理权重 |
| Kernel 证明义务 | 实例定义及与原定义相等所需定理 |
| 现有公开包装 | 是否必须保留当前签名与名字 |
| 真实计数影响 | 新增算法后，该声明本身是否仍为 `noncomputable` |
| 证据状态 | proved / refuted / blocked / unverified |

只有 Gate E 通过后才进入 G5，展开完整候选依赖闭包及 Examples 影响分析。只有当报告要给出整个主库的精确可覆盖数量时，才必须把深表补齐到全部主库声明；否则必须把未进入深表的行计入 `unverified`，不能用抽样结果外推。

计数必须拆开报告：

- 主库与 `Examples/`；
- 直接依赖与传递依赖；
- `Kernel.deterministic`、`Kernel.comp`、`Kernel.map`、`Kernel.prod`、`Measure.map`、`ProbabilityMeasure.map`、`Measure.dirac` 等不同根因；
- 可删除重复算法、可简化证明、仅能增加可执行入口、实际可移除 `noncomputable` 声明四种收益。

不得把 `dependency_propagation` 类别的数量直接解释为重构后可消失的数量，也不得把整个 137 声明中的依赖统计当成主库 58 声明的统计。

## 6. 第二阶段：先确定数学对象，再设计接口

### 6.1 初始探针只研究两个后端

初始探针必须只包含：

1. **有限、可执行的有理数次概率后端**；
2. **Mathlib `Kernel` 后端**。

原因是 EFG 的动作核在终止历史上可能是零 Kernel。归一化的 `FiniteLaw α` 总质量为 1，不能直接表达这种 killed/zero 分支；`Option (FiniteLaw α)` 也不能自动保证一般复合对次概率封闭。因此探针必须明确选择以下一种做法并论证：

- 在探针文件内部定义最小的有限有理数次概率／有限质量对象；或
- 证明目标子域永远归一化，并把终止性放在 Kernel 外部，使零分支不属于被抽象的对象。

如果第二种做法无法覆盖现有 `ActionPolicy.kernel` 等声明，必须如实标记覆盖失败。不得暗中用归一化 `FiniteLaw` 代表零 Kernel。

### 6.2 接口的形状

不要预先指定唯一接口。至少比较以下三个形状，并选择能以最少结构覆盖当前声明的一个：

1. 异宇宙二元概率态射 `K.{u, v} α β`；
2. law constructor `L β` 加上 bundled family `α → L β`，并显式携带 `Admissible`／`AdmissibleFamily`；
3. 以带结构对象为端点的范畴式接口。

排除的是不携带源对象条件或 family admissibility 的裸 `L : Type u → Type v`，因为任意 `α → L β` 不能自动解释为可测 Kernel。接口必须明确说明端点和态射的 admissibility：有限后端可能需要有限枚举、可判等或规范化结构，Kernel 后端需要可测空间、可测性和质量界证明。

至少分析下列运算是否必要，并给出每项的最小定律：

- 恒等态射；
- 复合／bind；
- 确定性态射；
- 零／killed 态射；
- 依据可判定状态的分段；
- 映射；
- 独立乘积、strength 或足以表达状态与新样本配对的操作。

接口中不得放入只为某个证明方便、却未被目标算法使用的操作。另一方面，不能通过省略零、分段或乘积来回避现有 EFG 一步执行的真实需求。接口或实例不得包含 EFG 专用的 `stepKernel`、`pathStepKernel`、`partialTraj` 等整段算法字段，不得按后端类型分支，也不得直接转发到一个已经完成全部 EFG 工作的现有定义。

分段不能只抽象成裸命题 `p : α → Prop`。必须说明共同的 admissible predicate 如何同时提供有限后端所需的判定能力，以及 Kernel 后端所需的集合可测性。若两种能力只能通过后端各自的附加参数获得，也要在接口中显式表达，不能依赖全局 `Classical.propDecidable`。

从有限后端到 Kernel 的解释也有范围限制：任意可计算函数 `α → FiniteSubLaw β` 并不自动关于任意 `MeasurableSpace α` 可测。探针必须选择并明确证明以下一种范围：

- 源和目标都是有限离散可测空间；
- 有限 Kernel 本身携带所需可测性证明；
- 通过一个明确的 object/admissibility 层限制可解释的端点。

不得把有限状态探针得到的解释定理陈述成任意可测空间上的通用转换。

还要区分两类质量条件：有限次概率要求每个输入点的总质量不超过 1，而 EFG action policy 可以在部分输入为零、其他输入为概率。不能未经证明地用全局的“整个 Kernel 为零或整个 Kernel 为 Markov”条件代替逐点条件。候选接口应把闭合的 subprobability/finite/s-finite 子域打包成态射，或为运算设置一个明确的 `Good` 条件，并证明确定性、零、复合、分段和实际使用的 strength 保持它。

若仓库中没有适合的有限次概率类型，探针内的默认最小对象是：有限的 `(outcome, ℚ≥0)` 表加总权重 `≤ 1` 的证明。需定义按每个 outcome 聚合质量的语义等价；不得直接把只适用于归一化 law 的 `FiniteLaw.Equivalent` 当成这个新类型的等价，也不得要求原子表的结构相等。

对每条代数律都要说明：

- 泛型算法的哪一步需要它；
- 有限后端如何证明；
- Kernel 后端如何证明；
- 该定律是定义相等、外延相等还是几乎处处相等。

## 7. 第三阶段：强制 Lean 探针

最终探针文件必须是独立模块，不能被稳定库导入。P0–P5 构成完整研究，但按下表门控执行；“必做”是指每项最终必须有明确状态，不是要求在前提已被推翻后继续编码。

| Gate | 内容 | 继续条件与停止条件 |
|---|---|---|
| A | P0 + P1a/P1b | 有限次概率对 zero/bind 闭合，Kernel 侧能表达逐点 killed；否则停止 |
| B | P2 | 确认同一泛型项、有限端可运行、Kernel 端与当前声明精确相等；任一失败则停止扩大范围 |
| C | P3a/P3b | P3b 失败时把结论退回普通一步执行，不得声称覆盖 EventPath |
| D | P4a/P4b | P4b 失败时不得推荐一般 finite-prefix 抽象 |
| E | P5a–P5e | 对前面通过的最强范围证明运算及交换图精确保真后，才可建议该范围内的表示多态层 |
| F | G5 | 仅在 Gate E 通过后展开完整库级收益和 Examples 依赖闭包 |

前置 Gate 被形式化反证时，下游状态写为 `not run: prerequisite refuted`。前置 Gate 只是 blocked 时，可以做一个最小的相邻诊断来定位缺口，但不能把未完成解释成数学上不可能。

最终持久化的 `RepresentationPolymorphismProbe.lean` 必须能够通过 Lean 检查。导致反证或编译错误的最小失败实验保留在 `/tmp`，在报告中记录命令、错误摘要和足以复现的代码片段；不得把故意不编译的代码写进最终探针。也不得用较弱的无关例子替代失败项。

### P0：最小接口与两种实例

比较第 6.2 节的候选形状，选出一个接口，定义实际被用到的运算及定律，并实现：

- 有限有理数次概率后端；
- Mathlib `Kernel` 后端。

必须验证异宇宙载体，而不是把所有类型降到 `Type 0`：

```lean
State : Type uS
Action : State → Type uA
ActionBundle : Type (max uS uA)
```

Kernel 端的可测性和质量条件必须来自接口中的对象／态射 admissibility。有限次概率端至少证明 zero、pure/deterministic、bind/comp 的总质量界和实际所需代数律。Kernel 实例与 Kernel specialization 可以使用 Mathlib 的 `noncomputable` 原语；泛型算法定义和有限后端的执行路径不能依赖它们，并且必须通过第 3 节要求的 pure-boundary 独立编译。

探针定义只需覆盖研究对象，不要在本轮把它设计成生产级公共 API，也不得把整段 EFG 执行藏进实例方法。

### P1：终止态零质量

P1 拆成两步：

- **P1a：闭合性。** 有限次概率后端的零对象总质量为 0；bind/comp 后仍满足总质量 `≤ 1`；至少用一个非归一化例子做机器检查。
- **P1b：EFG killed 分支。** 把终止历史的动作选择确实建模为零／killed 态射，并证明有限解释在 Kernel 端与当前 `KernelArena.Policy.toMeasurableKernel` 的终止分支精确相等。

明确区分两种终止语义：`Policy.toMeasurableKernel`／`ActionPolicy.kernel` 在终点没有动作质量，是 killed；`MeasurableKernelArena.ActionPolicy.stepKernel` 在终点使用 `Kernel.id`，是吸收状态转移。不得用后者的归一化 Dirac／id 分支冒充前者的零质量测试。

同时给出简短的类型或数学论证，说明普通归一化 `FiniteLaw` 为什么不能单独承担 killed action policy；如果现有 `FiniteLaw` 实际已经支持次概率，则用当前源码推翻这一判断。若 P1a 或 P1b 失败，不能继续声称有限后端覆盖 killed policy。

### P2：同一个一步执行算法

先定义一次表示无关的 arena、policy、动作后继复合和终止吸收步骤，然后分别选择两个后端实例化。玩具 arena 只可用于求值，不足以通过 P2；Kernel 端还必须对齐当前产品声明：

- 泛型动作复合在 Kernel 实例下与 `MeasurableKernelArena.ActionPolicy.actionStepKernel` 精确相等；
- 泛型终止吸收步骤与 `MeasurableKernelArena.ActionPolicy.stepKernel` 精确相等；
- 使用当前 `MeasurableKernelArena` 的实际可测空间和假设，不得为了消除证明义务而把任意现有空间替换成 `⊤`。

有限端应说明它与当前 `KernelArena.stepLaw`、`StateHistoryPolicy.stoppedStepLaw` 或当前最接近的一步算法的关系；若签名不同，给出明确适配器和等价定理，而不是另写一个同名玩具算法。

通过标准：

- 有限实例有真实运行结果，并至少用一个 `#guard`、`native_decide` 或结果等价定理把预期值变成会在错误时导致编译失败的机器检查；
- Kernel 实例与使用现有 Kernel 原语直接写出的参考定义通过 `Kernel.ext` 或更强的精确等式相等；
- 两个实例使用的是同一个泛型算法项，而不是两个手写实现；
- 泛型定义和有限实例执行路径不依赖 `Classical.choice`、`Classical.propComplete`、`sorryAx`、`unsafe` 或已有 `noncomputable` Kernel 值；Kernel 实例和 Kernel specialization 可以因 Mathlib 的 Kernel 构造局部使用 classical/noncomputable，但不得污染有限执行路径；
- 终止分类器在有限端是显式算法，并带有它与 `IsEmpty (Action state)` 等数学命题一致的证明；若仅要求调用者提供一个 `Decidable` 实例，把这项 API 代价单独记录。

### P3：依赖载体的 EventPath 片段

P3 分成两级，并始终保留独立的 `uS`、`uA`：

- **P3a：dependent Sigma。** 覆盖当前 `ActionBundle` 与 `recordedTransition` 的“保留动作并采样后继”链。优先判断它是否可由 strength 表达，并在 Kernel 端证明该 strength 与当前 `Kernel.id ×ₖ transition` 形式的构造精确一致。
- **P3b：dependent Pi。** 泛型化当前 `MeasurableKernelArena.EventHistoryActionPolicy.actionStepKernel` 或 `pathStepKernel` 实际经过的完整载体链，必须同时经过 `EventAt`、`Finset.Iic` 索引的 dependent `Pi` 前缀、终止谓词和当前 measurable instances。

有限实例需要机器检查的真实求值；Kernel 实例必须使用当前定义的可测空间、建立必要可测性并与原声明精确相等。普通笛卡尔积、只含 Sigma 或固定 `Type 0` 的探针均不足以通过 P3b。

### P4：有限前缀递归

P4 分成两级：

- **P4a：具体前缀。** 在非平凡、至少两步的示例上真实求值，并用机器检查固定预期结果。
- **P4b：一般有限 horizon。** 对任意 `start steps : ℕ` 或当前 API 对应的参数证明递归定理；有限端连接当前 `StateHistoryPolicy.prefixLawFrom` 或 `EventHistoryPolicy.prefixLawFrom`，Kernel 端连接当前 `Kernel.partialTraj` 及 `Simulation/Kernel/FiniteExecution.lean` 中相应的精确桥。

必须报告 P4 所需接口是否比一步执行严格更强。只有 P4a 通过而 P4b 未通过时，结论只能覆盖该固定探针，不能称为一般 finite-prefix 表示多态。

本探针不包括无限 `Kernel.traj`，也不能由有限前缀的成功推断无限路径律可计算。

### P5：表示解释的交换定理

P5 按以下顺序拆分，每一级只证明前面探针实际使用的结构：

- **P5a：两层解释。** 先定义单个有限次概率 law 到 `Measure` 的解释；再在有限离散可测空间或显式携带 family measurability 的范围内定义 family 到 `Kernel` 的解释。两者不可混为一个自动成立的步骤。
- **P5b：基本运算。** 证明解释保持 deterministic、zero 和 comp/bind。
- **P5c：分段。** 证明可判定且可测的 admissible predicate 下，有限分段与 `Kernel.piecewise` 相容。
- **P5d：配对。** 证明 P3 实际采用的 strength／product 相容；若 strength 已足够，不要求为了完整性另建一套未使用的独立乘积理论。
- **P5e：交换图。** P2 通过时必须证明一步执行交换图；P4b 通过时再证明任意有限前缀交换图。若 P3b 或 P4b 未通过，仍可对普通一步执行完成 P5，但结论范围必须相应收窄。

核心验收是与当前 Kernel API 的精确等式。若只能证明几乎处处相等，可以记录为较弱结果，但 G3/G4 不通过，也不能据此建议替换当前精确 API。

报告中必须把两个命题分开：G3 检查泛型 Kernel 项是否能在当前一般 `MeasurableKernelArena` 的实际可测空间上复现现有定义；G4 检查有限计算在离散端点或显式携带可测性时是否经解释映到相同 Kernel。不得用 G4 的离散 `⊤` 实例代替 G3 的一般可测空间证明。

先检查当前库是否已有诸如 `measure_stoppedStepLaw_eq_pathStepKernel` 的精确桥。若已有，P5 的新增价值是验证“同一泛型算法与运算解释相容”，不能把它描述为首次证明有限算法与分析 Kernel 一致；应比较新交换定理与现有桥各自覆盖的对象和假设。

有限分布的等价默认按每个 outcome 的聚合概率质量判断：归一化 `FiniteLaw` 可使用现有 `FiniteLaw.Equivalent`，新有限次概率类型必须使用它自己的外延等价。只有在规范化顺序也是接口合同的一部分时，才可以把底层原子列表结构相等当成语义相等。

## 8. `EffectiveKernel` 单独审计

现有 `EffectiveKernel SourceCode TargetCode` 若是对事件代码的期望变换器，则它与 carrier-level `α → law β` 的概率态射方向和数据不同。必须先审计以下能力：

- 是否有零算子；
- 事件语言是否对分段／状态限制封闭；
- 是否能表达源状态与目标样本的乘积或 strength；
- 是否能表达 EFG 一步执行所需的依赖载体；
- 组合后是否仍能产生足够的事件代码；
- 与有限后端或 Kernel 后端的语义映射是什么。

只有这些义务都有形式化实现与定律后，才可称 `EffectiveKernel` 为同一接口的第三实例。本轮允许把结果写成独立的“可行／不可行／需要扩展事件语言”结论，不要求为了凑齐第三实例而扩张产品 API。

## 9. continuation 与 conditioning 的当前状态审计

先核对当前 `Simulation/Continuation/Conditioning.lean`。若当前库已经有：

- 不依赖标准 Borel／`Nonempty` 的显式 continuation tail kernel；
- 基于 `condDistrib` 的 conditional tail kernel；
- 在正概率原子或几乎处处意义下连接二者的定理；

则本轮只记录它们的现状、使用者与剩余缺口。不得把已有结果再次列成待实现目标。

不能用显式 continuation 无条件替换 conditional kernel：两者在零概率前缀上的语义可能不同。若建议后续迁移，必须逐消费者说明所需语义和等价条件。

## 10. Classical 依赖审计

对审计脚本标记的 `Classical.propDecidable` 依赖，同时检查源码和 `#print axioms`／环境依赖信息。区分：

1. 有限状态上的局部可判定分支，可通过显式 `Decidable` 或枚举算法处理；
2. 由证明写法引入、可局部消除的 classical 依赖；
3. 无限时间上的“最终吸收／存在某时刻”等性质，其判定或见证搜索本身未必可计算；
4. 仅在外层语义包装或证明中存在、不会污染有限算法路径的依赖。

不得把“调用者提供命题真假或存在见证”包装成库已经计算出答案。新增显式 `Decidable p` 会改变签名；必须把这类方案列为 API 代价，而不是零成本消除。

## 11. 证据标准

每个“可计算”结论至少需要以下证据：

- `Lean.isNoncomputable` 或等价环境检查；
- 一个真实 `#eval`、`native_decide` 或编译后运行结果；
- 对泛型定义及有限实例的源码依赖审计，确认没有通过已有不可计算值偷渡结果；
- `#print axioms` 或等价公理审计；
- 与 Kernel 参考定义的形式化等式；
- 若涉及有限到 Kernel 的转换，提供保持运算的交换定理。

仅有 `Lean.isNoncomputable` 返回 false 不足以证明目标算法有可用的执行内容。仅有一个 Kernel `ext` 定理也不足以证明两个后端来自同一算法。

每个“不可行”结论必须区分：

- 数学或类型上的矛盾；
- 当前接口缺少必要结构；
- Mathlib 缺少现成引理；
- 在本轮时间内未完成。

后三类应标记为 blocked 或 unverified，不能写成数学上不可能。

## 12. 性能证据

编译时间只作诊断，不作核心可行性判据。若报告性能数据：

- 使用已存在的 Mathlib 缓存；
- 对空白探针、有限后端探针、双后端探针分别运行；
- 每项至少三次，报告预热后的中位数；
- 同时报告文件行数、声明数和关键实例数量；
- 不把单次墙钟波动解释为架构优势。

## 13. 明确的语义边界

即使 P0–P5 全部成功，也必须保留下列一般边界：

- 有限前缀算法不等于无限路径律；
- `Kernel.traj` 一般仍属于分析语义；
- 正则条件分布在零概率条件点上的版本选择不能由有限枚举自动解决；
- 连续状态、一般可测空间、积分和 a.e. 语义不能由有限有理数对象完整替代；
- 保持现有 Kernel／Measure 返回类型与公开名字时，相应包装声明可能仍为 `noncomputable`；
- 增加可执行入口、复用算法、简化证明与减少 `noncomputable` 数量是四个不同结果。

## 14. 决策规则

报告必须分别给出以下结论，不得只给一个总括性的“可行／不可行”：

| 子问题 | 允许结论 |
|---|---|
| 普通一步执行 | proved / refuted / blocked / unverified |
| 终止态 killed 语义 | proved / refuted / blocked / unverified |
| 依赖 EventPath | proved / refuted / blocked / unverified |
| 有限前缀递归 | proved / refuted / blocked / unverified |
| 有限到 Kernel 的语义交换 | proved / refuted / blocked / unverified |
| `EffectiveKernel` 作为同一后端 | proved / requires extension / refuted / unverified |
| 全 Simulation 层适用性 | exact scope with exclusions |
| 稳定 API 影响 | additive / signature-changing / incompatible |
| `noncomputable` 数量影响 | exact proven set or bounded range |

只有在完整逐声明矩阵和传递依赖闭包都支持时，才可以复述诸如“主库约 30 个”或“Examples 约 48 个”之类的数字。否则把它们明确标为未经验证的旧假设，并给出：

- 已形式化证明可覆盖的下界；
- 有条件可覆盖的范围；
- 已知不能覆盖的集合；
- 尚未验证的集合。

最终架构建议必须从以下选项中选择并说明证据：

1. 保持当前双层设计，只补充局部算法；
2. 在内部增加一步执行／有限前缀的表示多态骨架，现有 API 作为语义包装；
3. 扩展到更大范围的 Simulation 重构；
4. 放弃该方向。

若证据只支持局部复用，不得推荐全库迁移。

## 15. 报告结构

`REPRESENTATION_POLYMORPHISM_FEASIBILITY.md` 至少包含：

1. 执行时基线与工作区状态；
2. 当前架构事实；
3. 数学对象与最小接口；
4. P0–P5 的代码位置、命令、结果与失败证据；
5. `EffectiveKernel` 独立审计；
6. continuation／conditioning 现状；
7. Classical 依赖分类；
8. 逐声明矩阵或其机器可检查来源；
9. 主库和 Examples 分开的依赖闭包；
10. 语义、API 和可计算性边界；
11. 分项 verdict；
12. 若建议实施，给出可回退的最小迁移顺序和每一步停止条件。

引用源码时使用当前仓库中的实际路径和声明名。任何近似数字都要标注统计口径和命令。

## 16. 结束检查

完成后运行与本任务相称的检查：

```bash
lake env lean docs/research/efg-computability/RepresentationPolymorphismProbe.lean
python3 scripts/check_lean_placeholders.py \
  docs/research/efg-computability/RepresentationPolymorphismProbe.lean
python3 scripts/check_efg_api_growth.py
python3 scripts/check_efg_computability.py
python3 scripts/check_efg_governance.py
git diff --check
git status --short --branch
```

另外对两个未跟踪研究产物单独检查行尾空白；`git diff --check` 默认看不到未跟踪文件。重新生成受保护产品目录的 diff、状态和内容哈希，与开始快照逐字比较。若全局检查因开始前已有修改失败，把既有失败和本任务新增失败分开报告，不得修改或清理用户原有工作来取得绿色结果。

对比开始和结束状态。除两个允许的研究产物外，不应产生本任务的新修改；开始前已有的修改必须原样保留。最终答复只报告：

- 两个产物路径；
- P0–P5 的分项结论；
- 推荐的架构选项；
- 已证明的覆盖范围与仍未验证的范围；
- 检查结果；
- 工作区是否只增加了允许的研究产物。
