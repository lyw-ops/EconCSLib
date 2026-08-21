# EVE concise handoff

Last updated: 2026-08-21

## Repository checkpoint

- Local repository: `/Users/lyuyuwei/Documents/EconCSlib`
- Fork: <https://github.com/lyw-ops/EconCSLib>
- Experimental branch: `experiment/eve-stage5a`
- Handoff-policy checkpoint: `1258e05` (`docs(eve): define handoff repository policy`)
- DEV-001 WIP checkpoint: `07a48d3` (`WIP: prepare Stage 5A guidance liveness protocol`)
- Long-term route authority: `experiments/eve/README.md`
- Current gate authority: `experiments/eve/READINESS.md`

Always verify the live branch, HEAD, upstream, and worktree instead of assuming
the checkpoint above is still current.

## Handoff repository policy

- Treat <https://github.com/lyw-ops/EconCSLib> as the canonical handoff
  repository for this work.
- At the end of every completed task, update this handoff document with the
  completed scope, validation results, execution status, remaining blockers,
  and next bounded task.
- Commit and push every completed task's in-scope tracked changes to the
  current experimental branch on that repository; completed tracked work must
  not remain local-only.
- Stage only files owned by the completed task. Never mix unrelated or
  user-owned worktree changes into a handoff commit.
- Before declaring handoff complete, verify the pushed branch and commit and
  confirm that every tracked input needed to reproduce the result is present
  in the handoff repository. Ignored runtime evidence remains governed by the
  local-evidence policy below.

## Research direction

EVE studies generated Lean proofs for algorithmic game theory with deterministic
filtering and Codex AI review. The central mathematical design has two routes:

1. **Direct route:** prove the exercise using concrete objects close to the
   statement.
2. **Transport route:** encode the exercise into the abstract objects used by
   an existing general theorem, build a `RefinementCertificate` proving that
   exercise assumptions establish theorem assumptions, instantiate the theorem,
   and transport its conclusion back to the exact concrete exercise statement.

Ordinary tasks may use either route. Paired experiments keep the two solver
workspaces independent and compare them only through deterministic evaluation.

Model order remains Luna for low-cost engineering and liveness development,
then Sol for an equal-condition full replication only after the protocol is
valid and the Luna gate has closed.

## Completed stages

- Stage 0: EvE sidecar scaffold and local deterministic smoke infrastructure.
- Stage 1: local deployment and bounded Luna manual smoke; smoke 002 scored
  `1.0` after the isolated Lean toolchain repair.
- Stage 2: Entry Game direct/transport pair, accepted fixtures, agreement
  evaluator, and 12 rejected mutations.
- Stage 3: public review micro-benchmark with Codex AI review; no mutation false
  accept and no claim of independent human review.
- Stage 4: protocol `EVE-STAGE4-LUNA-ENTRY-GAME-DEV-002`; all 12 cells and 24
  Luna sessions completed once and were machine re-audited. Direct run success
  was static `1/2`, fixed `2/2`, evolved `2/2`; transport was static `1/2`,
  fixed `0/2`, evolved `0/2`. All evolved rollouts produced zero optimizer
  candidates, so Stage 4 does not demonstrate guidance evolution.

Stage 4 tracked records and local `.runtime` evidence are historical and must
not be rewritten or deleted.

## Current Stage 5A state

Protocol `EVE-STAGE5-LUNA-ENTRY-GAME-GUIDANCE-LIVENESS-DEV-001` is invalidated
in full before execution. The WIP checkpoint, detached hash, original Codex AI
review, and four blockers are preserved; it created zero Stage 5A run roots and
started zero model sessions.

The executed protocol is
`EVE-STAGE5-LUNA-ENTRY-GAME-GUIDANCE-LIVENESS-DEV-002`, version `2.0.0`, hash
`6dafcb0d2476cd2f21df0c976f4f380488f1dcec067d7a0e7ba0802631045a05`.
Its immutable launch status remains `FROZEN_NOT_YET_EXECUTED`; do not rewrite
that frozen historical input after execution. The pre-execution review is
`stage5a_review/dev002-audit.json`, and the tracked post-execution record is
`stage5a_review/dev002-execution-audit.json`.

All 12 cells and 36 Luna sessions completed once in frozen order with fresh run
roots, zero retry/resume/import, and ledger exit code zero. The 12 machine
audits reproduced byte-identically. Raw candidate passes were direct static
`0/6`, fixed `0/6`, evolved `0/6`; transport static `3/6`, fixed `2/6`, evolved
`1/6`. Four failure-derived guidance candidates were produced and admitted.
One candidate from direct/2718/evolved iteration 1 was selected in iterations 2
and 3, giving one valid local `GUIDANCE_PRODUCED_AND_SELECTED_LATER` chain.

Post-run review found a blocking frozen-checker defect. The isolated solver used
Python 3.9.6, while both immutable checkers record timestamps through
`datetime.UTC`, which is unavailable before Python 3.11. All 36 sessions hit the
defect at least once (91 failed invocations). Runtime workarounds yielded 57
valid recorded events in 11 sessions, but 25 rollouts retained an empty check
list. The existing auditor permits an empty list, so its pass does not establish
the full per-edit feedback contract. Preserve DEV-002 as executed historical
evidence: do not retry it or silently repair its frozen artifacts. The ordinal-6
chain is a genuine local mechanism observation, but the whole matrix is not a
clean protocol execution and does not authorize Sol replication.

## Last verified evidence

At this handoff:

- The frozen Lean entry target built successfully (`3096` jobs).
- 75 EVE tests passed; 2 environment-dependent tests were skipped as designed.
- The DEV-002 detached protocol hash and all frozen inputs verified.
- All 12 planned Stage 5A `--check` calls passed.
- Preflight wrote no DEV-002 run root or ledger and made zero model calls.
- All 12 execution attempts completed with exit code zero and consumed exactly
  36 Luna sessions; no retry, resume, or import occurred.
- The ledger contains exactly the frozen 12-cell order, and all 12 post-run
  audits reproduced byte-identically.
- Post-run transcript review found the checker-runtime defect above in all 36
  sessions; 25/36 rollouts have no recorded check event.

These records establish raw public-development execution and one local liveness
chain only. They do not establish a clean comparison, causal EvE effect, model
capability, benchmark readiness, evaluation completion, or Sol readiness.

## Next bounded task

Stop after recording the executed DEV-002 defect. Preserve all Stage 4 and
Stage 5A runtime evidence and unrelated worktree changes. The next bounded task
is review-only preparation of a new protocol identity, normally DEV-003: use a
Python-3.9-compatible UTC expression, execute the immutable checker with the
exact solver runtime during preflight, make missing required check evidence fail
closed, add regressions, use fresh roots and a fresh ledger, and obtain a new
review. Do not execute DEV-003 or start Sol without separate user authorization.

## Local versus GitHub evidence

GitHub stores tracked code, documentation, and commit history. Runtime evidence
under `experiments/eve/.runtime/` is ignored and remains only on this machine.
A fresh clone or cloud task must not claim that the missing runtime directory
means the historical runs did not occur; use tracked audit hashes and request
the local evidence when full re-verification is required. The DEV-002 execution
hashes, raw outcomes, liveness events, and checker defect are tracked in
`stage5a_review/dev002-execution-audit.json`.

The current mixed worktree also contains 47 locally modified Lean files whose
hashes are frozen by `stage5a_lean_environment.json` but whose changes are not
owned by the EVE handoff task. They must not be staged without separate
authorization. Consequently, the EVE protocol and execution audit can be pushed
independently, but a fresh clone of the handoff repository cannot yet reproduce
the frozen local Lean environment. Resolve that scope explicitly or prepare a
successor protocol against a clean committed Lean tree before claiming a
repository-complete handoff.

## Bootstrap prompt for the next conversation

Copy the following prompt into the next Codex conversation. It is intentionally
complete enough to establish the historical result, the current blocker, the
next bounded task, and the stop conditions without relying on chat history.

```text
打开 `/Users/lyuyuwei/Documents/EconCSlib`，在分支
`experiment/eve-stage5a` 上继续 EVE Stage 5A。先核对事实，再修改；不要仅凭这段提示词
假定仓库状态没有变化。

首先完整阅读并遵守仓库根 `AGENTS.md`（若由系统提供，也要按其全文执行），然后完整阅读：

- `experiments/eve/AGENTS.md`
- `experiments/eve/HANDOFF.md`
- `experiments/eve/README.md`
- `experiments/eve/READINESS.md`
- `experiments/eve/stage5a_review/dev002-execution-audit.json`

同时检查 `git status --short --branch`、最近提交、所有 remotes、目标文件及相邻实现，核对
分支是否仍跟踪 `fork/experiment/eve-stage5a`。交接仓库是
`https://github.com/lyw-ops/EconCSLib`；DEV-002 的已推送执行归档点是提交
`9269f3ea991e8e7e099dd541b870f37331796dc6`。工作区包含大量用户拥有的无关修改，
必须完整保留；只能暂存并提交本任务实际拥有的文件，不能顺手格式化、还原或提交其他修改。
每次任务完成后必须更新 `experiments/eve/HANDOFF.md`，将本任务改动提交并推送到该
交接仓库的当前分支，再核对远端提交确实存在。

你需要掌握的历史事实如下：

1. Stage 4 已完成，但 evolved rollouts 没有产生 optimizer candidates，因此没有证明
   guidance evolution。Stage 4 的 tracked records 和本地 `.runtime` 证据都必须保留。
2. Stage 5A DEV-001 在执行前整体作废；它没有建立 run root，也没有启动模型会话。
3. DEV-002 协议是
   `EVE-STAGE5-LUNA-ENTRY-GAME-GUIDANCE-LIVENESS-DEV-002`，版本 `2.0.0`，
   hash 为
   `6dafcb0d2476cd2f21df0c976f4f380488f1dcec067d7a0e7ba0802631045a05`。
   其冻结输入里的 `FROZEN_NOT_YET_EXECUTED` 是不可变历史字段，执行后也不能重写。
4. DEV-002 已按冻结顺序执行完 12/12 cells、36/36 Luna sessions；无 retry、resume、
   import，ledger 全部 exit code 0，12 个 post-run machine audits 可字节级复现。
   raw candidate passes 为：direct static `0/6`、fixed `0/6`、evolved `0/6`；
   transport static `3/6`、fixed `2/6`、evolved `1/6`。共生成并 admitted 四个
   failure-derived guidance candidates。direct/2718/evolved iteration 1 产生的
   `optimizer_2507e8392dc3` 在 iterations 2 和 3 被再次选择，形成一个真实的本地
   `GUIDANCE_PRODUCED_AND_SELECTED_LATER` liveness chain。
5. DEV-002 同时存在阻断性冻结 checker 缺陷：isolated solver 是 Python 3.9.6，
   immutable checkers 却调用 Python 3.11 才有的 `datetime.UTC`。36/36 sessions
   至少触发一次该错误，共 91 次失败 checker invocations。运行时 workaround 只让
   11 个 sessions 留下 57 个有效 recorded events；25/36 rollouts 的 check list 为空。
   现有 auditor 错误地允许空 list。因此 DEV-002 只能作为“执行过但协议不干净”的历史
   证据：它支持 raw external-evaluator observations 和一个本地 liveness mechanism
   observation，但不支持 clean comparison、causal EvE effect、model capability、
   benchmark readiness、evaluation completion 或 Sol readiness 的主张。
6. DEV-002 的所有尝试和 36 个 Luna sessions 都已消耗。绝对不要 retry、resume、
   import、修补后续跑、重写冻结工件或复用其 runtime/population/guidance/candidate/session。
   不要删除或改写 Stage 4/DEV-001/DEV-002 历史证据。
7. `.runtime` 被 Git 忽略，只存在于这台机器；GitHub 上的
   `stage5a_review/dev002-execution-audit.json` 是 tracked 摘要。缺少 `.runtime` 的
   fresh clone 不能反过来否认历史执行，但完整复核需本机证据。
8. `stage5a_lean_environment.json` 冻结的 Lean closure 与当前混合工作区中 47 个
   用户拥有、尚未提交的 Lean 修改相交。这 47 个文件不属于当前 EVE 任务，未经另行
   明确授权不能暂存或提交。因此当前 fork 的 fresh clone 尚不能复现 DEV-002 当时冻结的
   本地 Lean environment。后继协议必须解决这个来源边界，不能掩盖它。

你的本次任务是：仅准备、验证、审查并冻结一个新的 Stage 5A 开发协议身份（通常命名为
DEV-003），以修复 DEV-002 暴露的 checker/runtime、preflight 和 fail-closed 证据缺陷。
这是 review-only / zero-model-call 的协议工程任务。完成可复核交接后立即停止；未经用户
另行明确授权，不得执行 DEV-003，不得消耗 Luna quota，不得开始 Sol replication。

DEV-003 至少必须满足以下要求：

- 使用新的 protocol ID、version、detached hashes、fresh run-root parent 和 fresh
  attempt ledger；绝不复用 DEV-002 的执行状态或工件。将 DEV-002 保留为
  executed-but-defective historical evidence，通过新的 supersession/准备记录前进，
  不得静默修补旧冻结协议。
- immutable checker 必须兼容 exact isolated solver 的 Python 3.9.6，例如使用
  `datetime.timezone.utc` 而不是 `datetime.UTC`；同时核对所有 checker entry points，
  不能只修一份副本。
- safe preflight 必须在 disposable workspace 中，以计划执行时完全相同的 isolated
  solver Python、checker 文件、Lean 工具链和入口实际运行 immutable checker；必须
  验证一次真实 check event 被记录，并检查真实 Lean stdout/stderr/exit status。这个
  preflight 必须保持零模型调用、零 Luna quota、零正式 run root、零正式 ledger 写入。
- wrapper、auditor 和 protocol contract 必须 fail closed：凡是冻结契约要求 checker
  反馈的 rollout/candidate edit，缺少、为空、解析失败或与候选不匹配的 check evidence
  都必须导致失败。明确并冻结“何时至少需要一个有效 checker event”的规则；空 check
  list 不能再被 machine audit 接受，也不能由失败事件伪造 liveness。
- 添加覆盖 Python 3.9 compatibility、exact-runtime safe preflight、missing/empty check
  rejection、malformed/mismatched event rejection、no false liveness、fresh ledger/order
  的回归测试；检查已有相邻 Stage 5A 测试，避免重复或削弱断言。
- 解决可复现的 Lean source boundary。不要提交那 47 个用户文件。优先把 DEV-003 冻结到
  一个干净、已提交、fresh-clone 可验证的 Lean tree；如果在不纳入这些用户修改的前提下
  无法忠实确定目标，就停止并把准确 blocker 与所需授权写入 HANDOFF，而不是猜测、复制
  或扩大任务范围。宣称 DEV-003 review ready 前，fresh clone 必须能验证其冻结环境。
- 更新所有受影响的 protocol、review/audit、README、READINESS 和 HANDOFF 记录，使
  DEV-001 invalidated、DEV-002 executed-defective、DEV-003 frozen-not-executed 三者语义
  清楚且不可混淆。不要把 natural-language claim 当成机器验证。

按改动风险运行验证，至少包括：完整 EVE tests、相关 Stage 5A targeted tests、protocol
verifier、所有计划单元的 `--check`/`--dry-run`、detached hash/environment verification、
`git diff --check`，并明确验证 DEV-003 的 preflight 没有模型调用、没有正式 run root、
没有正式 ledger、没有继承 DEV-002 state。若测试依赖环境而跳过，逐项说明，不能笼统称
“全部通过”。

最终只提交本任务拥有的 tracked files，先审查 staged diff，再 commit 和 push 到
`fork/experiment/eve-stage5a`。最后报告：新协议身份和 hash、具体修复、review 结论、
测试结果、zero-model-call 证据、fresh-clone reproducibility 状态、提交 hash 与 GitHub
链接，以及仍需用户授权的下一动作。停在 DEV-003 `FROZEN_NOT_YET_EXECUTED`；不要把
“准备完成”解释为执行授权。
```
