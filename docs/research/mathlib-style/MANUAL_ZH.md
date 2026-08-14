# Mathlib 风格与评审蒸馏手册

- **版本：** 0.3.1
- **状态：** Phase 3 normative revision complete
- **核查日期：** 2026-08-13
- **评测环境：** mathlib `v4.30.0` / commit `c5ea00351c28e24afc9f0f84379aa41082b1188f` / Lean `leanprover/lean4:v4.30.0`
- **机器可读规则：** `../../../benchmarks/mathlib-style/manifests/RULES.json`
- **验证器注册表：** `../../../benchmarks/mathlib-style/manifests/VALIDATORS.json`
- **来源注册表：** `../../../benchmarks/mathlib-style/manifests/SOURCES.json`

## 1. 文档定位

本手册将 mathlib 的风格、命名、文档、PR 评审与固定版本 linter 行为转换为可操作的评审规则。它不是 mathlib 官方政策文件，也不是完整格式化器。其用途是人工 review、review agent 检索、模型蒸馏以及 benchmark 构造。

mathlib 的代码行为固定在 `v4.30.0`；贡献指南不是 mathlib release 的组成部分，因此另行固定为 `MATHLIB-POLICY-2026-08-13`。两者不得混称为同一版本。

## 2. v0.3.1 对 v0.3.0 的规范补丁

- Phase 3 解决不可变 v0.3.0 manual adversarial audit 中全部 13 条 P1/P2
  finding。它修改规则文字与 validator/source metadata，不迁移 benchmark
  数据 schema。
- rule/manual artifact version 为 `0.3.1`；`schema_version` 与全部 11 个
  JSON Schema 继续 byte-for-byte 冻结在 `0.3.0`。
- 75 个 leaf rule ID、legacy aliases 以及 `PAIR` / `DETECT` / `REPAIR` /
  `LOCATE` 任务定义完全不变。
- 评测环境仍为 mathlib `v4.30.0`、commit
  `c5ea00351c28e24afc9f0f84379aa41082b1188f`、toolchain
  `leanprover/lean4:v4.30.0`；政策快照仍为
  `MATHLIB-POLICY-2026-08-13`、commit
  `7b967eb1aaab674bd6aead708d42c4a83e2aca05`。
- Unicode 验证改为引用固定 `linter.unicodeLinter` 实现与 allow-list；
  native-decision 硬验证把语法 linter 与真实固定 `leanchecker` gate 组合。
- Phase 3 不生成正式 benchmark case、训练数据、测试数据或 held-out 数据；
  benchmark 生产与独立标注仍属于 Phase 4。

## 3. 三类版本快照

| 快照 | 用途 | 固定方式 |
|---|---|---|
| evaluation environment | 编译、linter、导入工具行为 | mathlib `v4.30.0` + commit + toolchain |
| policy snapshot | 风格、命名、文档与 review 文字规范 | contributor-site commit `7b967eb1aaab674bd6aead708d42c4a83e2aca05` |
| source environment | 某个历史 PR 原始上下文 | 每个 case 单独记录 base/merge commit 与 toolchain |

## 4. 规则解释框架

### 4.1 Rule strength（规则强度）

- `MUST`：在声明范围内明确要求、禁止或由固定 validator 决定。
- `SHOULD`：默认应遵守；偏离需要具体理由。
- `PREFER`：社区偏好，存在多个合理选项。
- `CONTEXT`：依赖数学、架构或下游用途。

### 4.2 Automation level（自动化层级）

- `DETERMINISTIC`：固定 validator 在其文档化范围内可决定操作条件。
- `ASSISTED`：机器给出证据，仍需人工判断。
- `HUMAN`：不声称存在可靠自动判定程序。

### 4.3 Review priority（本次评审优先级）

`BLOCKING / SUBSTANTIVE / MINOR / INFORMATIONAL` 属于 finding，不属于规则本体。相同 `SHOULD` 规则在不同 case 中可能具有不同 review priority。

## 5. 核心规则集

本版包含 **75 条 leaf rules**。旧的 `FIL-002`、`FIL-004`、`DOC-001`、`DOC-002`、`NAM-010` 与 `LOC-002` 仅保留 alias 映射。

| Rule ID | 标题 | 强度 | 依据 | 自动化 | 操作规则 | Validator |
|---|---|---|---|---|---|---|
| `FIL-001` | 文件命名 | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | Lean 源文件通常使用 UpperCamelCase。极少数小写例外应先讨论；文件名还应反映其数学主题。 | `custom.file_name_upper_camel`, `human.file_topic_fit` |
| `FIL-002A` | 标准文件头格式 | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` | mathlib 文件以标准版权、Apache-2.0 许可证与 `Authors:` 文件头格式开始。 | `linter.style.header` |
| `FIL-002B` | 作者归属语义 | `CONTEXT` | `DIRECT_MANUAL` | `HUMAN` | `Authors:` 列表应标出在设计或开发上有实质贡献、维护者会就该文件联系的人；单靠格式检查不能决定作者归属。 | `human.authorship_attribution` |
| `FIL-003` | 模块与导入顺序 | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | 版权头后单独写 `module`。对于普通 `public import` 与 `import` 区块，每行一个 import、public 区块在前，并尽量在各区块内排序；对 `public meta import`、`import all` 等少见 modifier 不声称存在官方全序。 | `linter.style.header`, `custom.module_import_order` |
| `FIL-005` | 导入组织 | `PREFER` | `DIRECT_MANUAL` | `ASSISTED` | 每行写一个 import，保持 public/普通导入分组，组内优先按字母排序，并删除已证明冗余或无必要的导入。 | `custom.module_import_order`, `command.#min_imports_in`, `command.#redundant_imports`, `human.location_review` |
| `FIL-006` | 顶层对齐 | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | def、theorem、namespace、section、open 等顶层命令左对齐；不要因 namespace 或 section 而整体缩进。 | `linter.style.whitespace` |
| `FIL-007` | 文件内聚与规模 | `CONTEXT` | `REVIEW_HEURISTIC` | `ASSISTED` | 按数学内聚性与依赖边界拆分文件。约 1000 行只是评审者重新检查拆分的信号；mathlib 的 `longFile` linter 在超过 1500 行时警告，而下游项目若未配置则没有该行数上限。 | `linter.style.longFile`, `human.location_review` |
| `FIL-008` | 文件头禁止导入 | `MUST` | `DIRECT_MANUAL` | `ASSISTED` | 不得引入 `Mathlib.Tactic` 桶式导入或固定 header linter 明确禁止的其他导入。`Lake.*` 只触发警告，且仅可在必要性评审、性能测试和有理由的 linter allowance 后保留。 | `linter.style.header`, `human.location_review` |
| `FMT-001` | 行宽 | `SHOULD` | `DIRECT_MANUAL` | `DETERMINISTIC` | 每行不超过 100 个字符；当前 linter 对包含 URL 等文档化情形允许例外。 | `linter.style.longLine` |
| `FMT-002` | 运算符空格 | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | 在 :、:= 和中缀运算符两侧留空格；换行时把运算符留在上一行末尾。 | `linter.style.whitespace`, `human.layout_review` |
| `FMT-003` | 缩进 | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | 一般续行增加 2 空格；多行定理陈述的续行增加 4 空格；证明体相对声明缩进 2 空格。 | `human.layout_review` |
| `FMT-004` | by 与 calc 的位置 | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | by 与 calc 放在后续证明或计算开始前的同一行，而不是单独占一行。 | `human.layout_review` |
| `FMT-005` | 显式声明类型 | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | 公共签名中的参数与返回值若省略类型会妨碍可读性或 API 理解，就应显式写出类型。可从 typed dependent context 清楚推断的 index、universe 或类似 binder（如 `{n}`、`{m}`）可以省略类型。 | `human.statement_review` |
| `FMT-006` | 绑定子格式 | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | 绑定子后留空格，并通常显式写出绑定变量的类型。 | `linter.style.whitespace`, `human.layout_review` |
| `FMT-007` | 匿名函数 | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` | 匿名函数必须使用 `fun`，而不是 `λ`。箭头 `↦` 只是轻微的源码偏好，不是硬性要求。 | `linter.style.lambdaSyntax` |
| `FMT-008` | 函数应用语法 | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` | mathlib 源码中不得使用 `$` 表示函数应用；应改用 `<|`。 | `linter.style.dollarSyntax` |
| `FMT-009` | 目标聚焦 | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | 通常应显式聚焦证明目标（常用 `·`），避免 tactic 无意作用于多个目标；只有在明确需要时才使用文档化的多目标组合子。 | `linter.style.multiGoal`, `human.proof_review` |
| `FMT-010` | 每行一个 tactic | `PREFER` | `DIRECT_MANUAL` | `HUMAN` | 通常每行只写一个 tactic；只有在确实提高可读性时才压缩短步骤。 | `human.proof_review` |
| `FMT-011` | 声明内部不留空行 | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | 在固定 `linter.style.emptyLine` 的适用范围内，不要用空白行切分 command，应以注释解释证明结构。其 deterministic 范围排除 doc/module doc、mutual command、string syntax、`where` fields、incomplete commands，以及路径含 `Tactic`、`Util` 或 `Meta` 的文件；范围外的同类可读性问题属于 assisted review。 | `linter.style.emptyLine`, `human.layout_review` |
| `FMT-012` | 生产代码中的 option 作用域 | `MUST` | `DIRECT_MANUAL` | `ASSISTED` | 移除以 `debug`、`pp`、`profiler` 或 `trace` 为 root 的开发期 option。固定 linter 还拒绝未局部化的 `maxHeartbeats` 类 option 与 `linter.flexible`，将 `linter.style.commandStart` 标为弃用，并拒绝新增 `backward.inferInstanceAs.wrap.reuseSubInstances` 技术债。其他确有技术必要的 production option 不自动失败，但必须尽量缩小作用域，并在要求时说明理由。 | `linter.style.setOption`, `human.layout_review` |
| `FMT-013` | 闭合 section 与 namespace | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` | 文件结束前应闭合 section 与 namespace，但文档化的最外层 public/meta/noncomputable section 例外除外。 | `linter.style.missingEnd` |
| `FMT-014` | 聚焦点语法 | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` | 使用 `·` 聚焦字符而不是普通句点，并且不要让聚焦点单独占一行。 | `linter.style.cdot` |
| `FMT-015` | Classical 的局部作用域 | `SHOULD` | `DIRECT_MANUAL` | `DETERMINISTIC` | 声明局部作用域足够时，不应在整个文件范围使用 `open Classical` 或 `open scoped Classical`。 | `linter.style.openClassical` |
| `FMT-016` | 使用 change 改变目标 | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` | `show` 若实际上改变目标，而不只是展示目标，应按固定版本 style linter 的要求使用 `change`。 | `linter.style.show` |
| `FMT-017` | Heartbeat 修改需局部化并解释 | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` | `maxHeartbeats` 系列 option 必须局部作用于单个命令，并附注释解释提高限制的必要性。 | `linter.style.setOption`, `linter.style.maxHeartbeats` |
| `FMT-018` | 任意宇宙使用 Type* | `SHOULD` | `REVIEW_HEURISTIC` | `HUMAN` | 表示任意宇宙层级时使用 `Type*` 而不是 `Type _`；只有确实需要并能说明元变量行为时才例外。 | `human.statement_review` |
| `FMT-019` | 可读且允许的 Unicode | `MUST` | `DIRECT_MANUAL` | `ASSISTED` | 拒绝固定 `linter.unicodeLinter` 不允许的字符与 variant-selector 用法；其 allow-list 依赖快照，并可能随 Mathlib 版本变化。允许字符是否提升数学可读性则另由人工评审。 | `linter.unicodeLinter`, `human.layout_review` |
| `NAM-001` | 语义化大小写 | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | Prop 项和定理使用 snake_case；Prop、Type、Sort 中的类型使用 UpperCamelCase；其他 Type 值通常使用 lowerCamelCase。 | `linter.style.nameCheck`, `environment_linter.defsWithUnderscore`, `human.naming_review` |
| `NAM-002` | 函数名服从返回类型 | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | 函数名的大小写由其返回类型的语义类别决定，而不是由“它是函数”这一事实决定。 | `human.naming_review` |
| `NAM-003` | 字段与构造子 | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | 结构字段和构造子遵循与普通声明相同的语义化命名规则。 | `human.naming_review` |
| `NAM-004` | 美式拼写 | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | 声明名使用美式英语拼写；文档正文可接受常见英语拼写。 | `human.naming_review` |
| `NAM-005` | 结论优先的定理名 | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | 定理名先描述结论，而不是复述证明方法或所有前提。 | `human.naming_review` |
| `NAM-006` | 用 of 表达前提 | `PREFER` | `DIRECT_MANUAL` | `HUMAN` | 需要在名称中表达前提时，把它们按陈述中的顺序放在 _of_ 之后。 | `human.naming_review` |
| `NAM-007` | 标准词汇 | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | 复用 mathlib 已有的标准符号词汇，例如 mul、add、one、zero、le、lt，而不要创造近义缩写。 | `human.naming_review` |
| `NAM-008` | 命名空间与点记法 | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | 当声明自然依附于某类型或对象时，放入相应命名空间并设计可用的点记法；不要把上下文重复编码进长名称。 | `human.naming_review` |
| `NAM-009` | 强制转换命名 | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | 强制转换声明按其底层函数命名，不使用泛化的 coe 名称掩盖语义。 | `human.naming_review` |
| `NAM-010A` | 外延性定理命名 | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | 外延性定理采用 `.ext`、`.ext_iff` 等既有命名，并在有依据时添加适当属性。 | `human.naming_review`, `human.api_review` |
| `NAM-010B` | 单射定理命名 | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | 根据定理形状采用 `f_injective`、`f_inj` 等既有单射命名模式。 | `human.naming_review` |
| `NAM-010C` | 归纳与递归原理命名 | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | 遵循归纳原理与递归原理的既有区分及参数顺序约定。 | `human.naming_review` |
| `DOC-001A` | 模块文档字符串的存在与位置 | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` | 除文档化的纯导入文件与初始化例外外，第一个非 import 命令必须是模块文档字符串。 | `linter.style.header` |
| `DOC-001B` | 模块标题与摘要 | `MUST` | `DIRECT_MANUAL` | `HUMAN` | 模块文档字符串必须包含一级标题，并对文件的数学内容给出有用摘要。 | `human.documentation_review` |
| `DOC-001C` | 相关模块章节 | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | 相关时按文档规定的顺序使用常规模块文档章节。`Main definitions` 与 `Main statements` 是可选 section；`Notation`、`References` 与 `Tags` 仅在文件内容相关时才要求。 | `human.documentation_review` |
| `DOC-002A` | 定义文档字符串 | `MUST` | `DIRECT_MANUAL` | `ASSISTED` | 每个公共定义都需要文档字符串，并说明其数学含义。 | `human.documentation_review` |
| `DOC-002B` | 主要定理文档字符串 | `MUST` | `DIRECT_MANUAL` | `HUMAN` | 每个主要定理都需要文档字符串；某个定理是否属于“主要定理”需要结合上下文判断。 | `human.documentation_review` |
| `DOC-002C` | 结构体与类字段文档 | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | 每个新出现的显式 structure 或 class field 默认都应有 docstring。有限例外包括 generated fields、只通过 `extends` 继承已文档化父项且没有新增显式字段的声明，以及上下文充分且真正自明的字段。 | `human.documentation_review` |
| `DOC-002D` | 有价值的引理文档 | `PREFER` | `DIRECT_MANUAL` | `HUMAN` | 普通引理若具有数学内容或可能跨文件复用，应添加文档字符串。 | `human.documentation_review` |
| `DOC-003` | 数学含义 | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | 文档使用英语并准确说明数学含义；可以抽象掉实现细节，但不能把实现描述冒充数学语义。 | `human.documentation_review` |
| `DOC-004` | 句子与定理格式 | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | 如果 docstring 是完整句子，应以句号结尾；有专名的数学定理按文档约定使用粗体。`linter.style.docString` 只检查 delimiter、空内容、首尾空白、尾随逗号与尾随换行形式等机械格式；句末标点、定理名称 boldface 和一般文风仍由人工评审。 | `linter.style.docString`, `human.documentation_review` |
| `DOC-005` | 交叉引用 | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | 当前 Lean 4 声明名用反引号标记；需要稳定链接时使用真实 fully-qualified name（如 `Set.mem_iUnion₂`），并显式交叉引用相关声明。普通 backtick 格式不证明名称可解析：计划中的 `custom.doc_link_check` 在固定环境中解析 exact name，而 namespace-relative、protected、alias、ambiguous 与 unresolved name 需分别处理并人工评审。 | `custom.doc_link_check`, `human.documentation_review` |
| `DOC-006` | 证明草图与注释 | `SHOULD` | `REVIEW_HEURISTIC` | `HUMAN` | 复杂或非显然证明应提供 proof sketch，并在证明中用注释标出数学阶段，而不是只保留 tactic 序列。 | `human.documentation_review` |
| `DOC-007` | 警告与适用范围 | `SHOULD` | `REVIEW_HEURISTIC` | `HUMAN` | 辅助性、危险性或适用范围很窄的声明，应在名称或文档中明确警告，避免被误当成公共首选 API。 | `human.documentation_review` |
| `DOC-008` | 文献引用 | `SHOULD` | `DIRECT_MANUAL` | `ASSISTED` | 形式化源自文献时，记录出处和结果的相关性；新的书目条目加入 docs/references.bib。 | `custom.bibliography_reference_check`, `human.documentation_review` |
| `STM-001` | 前提置于冒号左侧 | `PREFER` | `DIRECT_MANUAL` | `HUMAN` | 若证明一开始只是引入变量和前提，优先把它们写成冒号左侧参数，而不是最外层 ∀ 或 →。 | `human.statement_review` |
| `STM-002` | 避免合取前提 | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | 通常把 P ∧ Q 前提拆成独立的 hP 与 hQ，以提高 lemma 的可应用性。 | `human.statement_review` |
| `STM-003` | 拆分合取结论 | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | 公共 lemma 通常不要返回 Q ∧ R；分别提供两个结果，必要时由 private 合取 lemma 共享证明。 | `human.statement_review` |
| `STM-004` | 避免析取前提 | `PREFER` | `DIRECT_MANUAL` | `HUMAN` | 大多数情况下把 S ∨ T 前提拆成两个 lemma；只有拆分会造成大量近乎重复声明时才保留析取。 | `human.statement_review` |
| `STM-005` | 规范正规形 | `SHOULD` | `DIRECT_MANUAL` | `HUMAN` | 选择与 mathlib 现有 simp 方向和规范正规形一致的陈述，避免引入等价但不稳定的重写方向。 | `human.statement_review` |
| `PRF-001` | 复用已有引理 | `SHOULD` | `REVIEW_HEURISTIC` | `HUMAN` | 先搜索已有或更一般的结果，再写新证明；优先组合公共 API，而不是重做特殊情形。 | `human.proof_review` |
| `PRF-002` | 分解长证明 | `SHOULD` | `REVIEW_HEURISTIC` | `HUMAN` | 把长证明按数学步骤拆成可命名、可复用的辅助 lemma；不要只为缩短行数而隐藏结构。 | `human.proof_review` |
| `PRF-003` | 可读的 tactic 选择 | `PREFER` | `REVIEW_HEURISTIC` | `HUMAN` | 选择能表达数学意图、对重构较稳健的 tactic；代码高尔夫只有在不牺牲可读性时才是改进。 | `human.proof_review` |
| `PRF-004` | 稳定证明结构 | `CONTEXT` | `SYNTHESIZED_GUIDANCE` | `HUMAN` | 把脆弱展开、非常规透明度、反复使用 `erw` 或无法解释的额外 `rfl` 视为评审信号，而非自动违规；它们可能表明缺少 API lemma 或使用了非规范正规形。 | `human.proof_review` |
| `PRF-005` | 不保留无效 tactic 步骤 | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` | 删除不改变证明状态的 tactic 调用，但固定版本 linter 文档化的白名单与排除项除外。 | `linter.unusedTactic` |
| `PRF-006` | 避免弃用的 Lean 3 风格 tactic | `SHOULD` | `DIRECT_MANUAL` | `DETERMINISTIC` | 避免 `refine'`、`cases'` 与 `induction'`；除非存在文档化的不兼容性，应使用对应的 Lean 4 tactic。 | `linter.style.refine`, `linter.style.cases`, `linter.style.induction` |
| `PRF-007` | mathlib 证明中禁用 native_decide | `MUST` | `DIRECT_MANUAL` | `DETERMINISTIC` | mathlib 证明代码不得使用 `native_decide` 或 `decide +native`。硬验证必须组合 `linter.style.nativeDecide`（第一层语法检查，且对某些 `decide (config := ...)` 形式存在文档化 false negative）与固定的 `lake env leanchecker --fresh Mathlib` kernel/environment gate 或项目采用的等价检查。 | `linter.style.nativeDecide`, `checker.leanchecker` |
| `API-001` | 完整可用的 API | `SHOULD` | `REVIEW_HEURISTIC` | `HUMAN` | 按下游实际需要提供构造、消去、extensionality、simp/rewrite lemma 与属性，使用户无需展开实现细节。 | `human.api_review` |
| `API-002` | 命题式 API 优于定义偶然性 | `CONTEXT` | `SYNTHESIZED_GUIDANCE` | `HUMAN` | 当下游用户否则必须依赖偶然的定义相等时，优先提供稳定的命题式 API。反复出现 `erw` 或额外 `rfl` 只是需要调查的证据，并非普遍失败标准。 | `human.api_review` |
| `API-003` | 适当的一般性 | `CONTEXT` | `REVIEW_HEURISTIC` | `HUMAN` | 陈述应覆盖自然的一般情形并与相关文献和现有抽象一致，但不要为了形式上的最大一般性破坏可用性。 | `human.api_review` |
| `API-004` | 标准捆绑模式 | `CONTEXT` | `SYNTHESIZED_GUIDANCE` | `HUMAN` | 当现有捆绑抽象（如 bundled morphism、`FunLike` 或 `SetLike`）确实符合所建模对象时，应复用它们；不要把这些模式普遍强加于所有设计，并避免不必要的依赖类型或类型类 diamond。 | `human.api_review` |
| `API-005` | 适当的属性 | `CONTEXT` | `REVIEW_HEURISTIC` | `HUMAN` | 根据预期 API 与规范形决定是否添加 `@[simp]`、`@[ext]`、`@[simps]` 等属性；属性并非自动有益。 | `human.api_review` |
| `API-006` | 实例菱形安全 | `CONTEXT` | `REVIEW_HEURISTIC` | `HUMAN` | 检查新增实例是否产生非定义等价或非命题等价的菱形，以及非预期的推断路径。 | `human.api_review` |
| `API-007` | 变换生成的一致性 | `SHOULD` | `SYNTHESIZED_GUIDANCE` | `ASSISTED` | 普通适用情况下，应使用 `@[to_additive]` 或对偶生成等 transformation automation，并保持生成 API 与命名一致性。上下文例外包括 `to_additive existing`、companion declaration 已存在、unsupported constants、必要 naming override，以及生成结果会产生错误或不稳定 API 的情形。 | `human.api_review` |
| `LOC-001` | 正确归属文件 | `SHOULD` | `REVIEW_HEURISTIC` | `HUMAN` | 把声明放在数学主题合适且依赖允许的尽可能高层文件中。`#find_home` 只是证据，不是绝对可靠的位置判定器。 | `command.#find_home`, `human.location_review` |
| `LOC-002A` | 导入最小化 | `SHOULD` | `REVIEW_HEURISTIC` | `ASSISTED` | 避免不必要或过大的导入。使用 `#min_imports in` 对单个 command/term 向上查找依赖，并记录其 attribute/example 限制；使用通过 `#import_bumps` 启动的增量式 `linter.minImports`，从启用点向下跟踪后续 command 的 import 增长。两者都只是 assisted evidence，都不能证明全局架构最小性。 | `command.#min_imports_in`, `linter.minImports`, `command.#redundant_imports`, `human.location_review` |
| `LOC-002B` | 依赖方向 | `SHOULD` | `REVIEW_HEURISTIC` | `HUMAN` | 保持从基础模块指向高层模块的依赖方向；即使局部导入集合最小，只要造成架构循环或依赖倒置，也不合格。 | `human.location_review` |
| `LOC-003` | 重复与一般结果搜索 | `SHOULD` | `REVIEW_HEURISTIC` | `HUMAN` | 新增声明前，应使用 `exact?`、`apply?`、`#check` 和仓库搜索等工具查找相同、等价或更一般的结果。 | `human.location_review` |

### 5.1 Phase 3 finding 对 benchmark 标签的影响

- `FIL-003`：普通 public/ordinary import 区块内可判错；少见 modifier 间的相对顺序不得自动标错。
- `FIL-008`：`Mathlib.Tactic` 与明确禁用项为硬失败；`Lake.*` 是需必要性、性能和 allowance 证据的人工评审项。
- `FMT-005`：可清楚推断的 dependent index 省略类型可标为合法例外，不能仅因类型未写出就报错。
- `FMT-011`：只有固定 empty-line linter 的适用范围可用 deterministic 标签；排除项降为 assisted/human review。
- `FMT-012`：固定 option 类别可机器判定；其他技术性 option 依范围和理由评审，不得一概报错。
- `FMT-019`：机器标签绑定固定 `linter.unicodeLinter` 快照；“是否更可读”只由人工标签决定。
- `DOC-001C`：可选章节不得按缺失自动报错；conditional 章节只在内容相关时要求。
- `DOC-002C`：新显式字段默认需要文档，同时允许 generated、extends-only 与真正自明字段的有限例外。
- `DOC-004`：机械 docstring 格式与句末标点、boldface、一般文风必须分别标注。
- `DOC-005`：backtick 形式不能当作链接解析成功；exact fully-qualified name 与其他 Lean 名称解析形态分别评测。
- `PRF-007`：native-decision 标签需要语法 linter 与固定 `leanchecker` gate 的组合证据，并记录语法检查的 false negative。
- `API-007`：一般适用场景为 `SHOULD`，但列出的 transformation 例外不得标为违规。
- `LOC-002A`：两个导入工具的相反扫描方向与局部限制进入标签说明，任何一个都不能证明全局最小性。

## 6. 硬验证契约

可编译不等于合格。每个候选必须同时满足：

1. `lake env lean` 返回 0；
2. 候选代码不含 `sorry` 或 `admit`；
3. 候选代码不得新增 `axiom` 或 `constant` 声明；可信上下文只能位于冻结 prelude；
4. 目标声明相对 case baseline 不得产生新的公理依赖；不要求整个 mathlib 的公理集为空；
5. 不得存在未列入 case warning whitelist 的警告；
6. `PAIR`/`REPAIR` 声称保持 statement/specification 时，必须执行对应机器检查；
7. 源码、日志、metadata 与 validation record 通过 SHA-256 关联。
8. 若候选涉及 native decision，必须同时通过固定语法 linter 与 `lake env leanchecker --fresh Mathlib`（或项目采用并记录的等价 kernel/environment gate）。

静态扫描只是纵深防御。最终判断必须结合 Lean 编译、警告、公理差分、固定 linter 与固定 checker gate。

## 7. 规则卡字段

机器规则集中的每条 leaf rule 都包含：适用对象、例外、代表性 example、来源定位、规则强度、自动化层级、validator ID 和可用任务。Benchmark finding 必须指向 leaf rule，不能只引用旧的混合 alias。

## 8. 范围控制

来源覆盖矩阵位于 `../../../benchmarks/mathlib-style/manifests/COVERAGE.json`。局部变量字母约定暂不作为 pilot 评分项；性能 profiling 与全库迁移 campaign 属于其他 benchmark；AI 使用规范属于发布政策，不作为代码风格 gold 标签。

## 9. 使用边界

该材料用于离线评测与人工监督的 review suggestion。不得把 LLM 生成的 GitHub/Zulip 评论直接当作本人评论发布。真实 PR 样本的评论默认只保存 metadata 与人工释义，除非另行记录短引文依据。
