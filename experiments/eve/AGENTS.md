# EVE Agent Instructions

These instructions apply to all work under `experiments/eve/` and supplement
the repository-root `AGENTS.md`.

## Start every EVE task

1. Read `experiments/eve/HANDOFF.md` completely.
2. Inspect the current branch, recent commits, and `git status --short`.
3. Read the relevant sections of `experiments/eve/README.md` and
   `experiments/eve/READINESS.md`.
4. Read the active protocol, review record, and only the code needed for the
   current task. Do not scan the whole repository without a concrete reason.
5. Treat unrelated worktree changes as user-owned. Do not stage, rewrite,
   clean, or discard them.

## Authority and history

- `README.md` is the single authoritative long-term technical route.
- `HANDOFF.md` is the concise current-state index; it does not override frozen
  protocols, audits, manifests, or runtime evidence.
- Completed or attempted protocol evidence is append-only. Never silently
  rewrite an executed, invalidated, or reviewed outcome.
- A frozen protocol that needs a substantive repair must be explicitly
  invalidated or superseded under a new protocol ID/version before execution.
- Keep Stage 4 DEV-002 and its review/runtime evidence unchanged.

## Execution safety

- Do not run `--execute`, invoke Luna/Sol, consume model quota, retry a cell,
  resume/import a population, or begin Sol replication without explicit user
  authorization in the active task.
- `--check`, `--dry-run`, deterministic evaluators, tests, and read-only audits
  are allowed when relevant and must not dispatch a model.
- Do not cross the disabled private/formal experiment boundary.
- Preserve `experiments/eve/.runtime/`. It contains local evidence that is not
  stored on GitHub. Remove only individually verified, reproducible caches or
  temporary files when explicitly requested.
- Never claim independent human review. Codex review must be labeled
  `codex-ai-review`.

## Protocol and evidence requirements

- Freeze task, prompt, guidance, evaluator, budget, seeds, model identity,
  environment, failure policy, execution order, and all Lean dependencies that
  can affect the result.
- Keep direct and transport routes independent. The transport route must retain
  its full refinement-certificate and conclusion-transport obligations.
- Distinguish guidance changed, produced, admitted, selected later, and used.
  Do not infer one event from another.
- A failure-derived guidance claim requires machine evidence that the real Lean
  failure occurred before the relevant guidance change.
- Enforce one attempt per frozen matrix cell and the predeclared execution
  order before any model call.
- Provider model RNG is uncontrolled unless the adapter supplies and records a
  real provider seed; EvE sampler seeding is not end-to-end determinism.

## Verification and handoff

Scale verification to the change, but before freezing or executing a protocol
run at least:

```bash
python3 -m unittest discover -s experiments/eve/tests -v
python3 experiments/eve/scripts/verify_stage4_review.py --require-local-evidence
python3 experiments/eve/scripts/verify_stage5a_protocol.py
git diff --check -- experiments/eve
```

Run every planned cell's safe `--check` and `--dry-run` after protocol changes.
At the end of a material stage, update `HANDOFF.md`, `README.md`, and
`READINESS.md` together, record exact validation results, and state whether any
model call or EvE execution occurred.
