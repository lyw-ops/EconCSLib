# EFG 工作汇报

## 我们做了什么

我们为 EconCSLib 搭建了一套分层的扩展式博弈（EFG）结构：

- 使用 `Arena` 表示状态、合法行动和状态转移。
- 使用 typed `History` 记录完整行动历史，避免不同路径到达同一状态后被错误合并。
- 使用 terminal-aware execution，让执行在终局自动停止，不再要求终局提供不存在的行动。
- 使用 `ObservedGame` 表示玩家观察、信息状态和信息集上的策略。
- 使用 `ObservedChanceGame` 表示带机会节点和概率分布的博弈。
- 保留 `GameTree`、不完全信息博弈和 FOSG 等表示，并通过 compiler 连接到统一语义层。
- 增加 pure、behavioral、mixed strategy，以及 Nash、SPE、perfect recall 和 Kuhn equivalence 等语义。

完整 EFG 基线已经能够通过 Lean 构建、Examples 构建、placeholder 检查和架构治理检查。
