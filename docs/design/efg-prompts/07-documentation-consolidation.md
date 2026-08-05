# Prompt 07 — Consolidate EFG Architecture Documentation

You are working in the EconCSLib repository. Make EFG documentation easier to
navigate and harder to drift after the implementation tasks have landed.

## Current carrier scope

Read `docs/design/efg-minimal-core-freeze.md`. Documentation must reflect that
the compatibility freeze is deferred while retaining the universe and import
regressions. Do not alter Lean carrier declarations in this documentation
task.

## Problem

Architecture, facade closures, lifecycle status, migration history,
preservation strength, and research roadmaps are spread across many partially
overlapping notes. Repeating volatile module counts and ownership claims by
hand risks inconsistency.

## Required work

1. Build a claim inventory for all `docs/design/efg-*.md`,
   `docs/design/extensive_game.md`, and the EFG section of `docs/design.md`.
   Mark each repeated claim and its current authoritative source.

2. Establish this authority order:

   - Lean source for declarations and proofs;
   - `efg-minimal-core-freeze.md` for freeze readiness and current regressions;
   - `efg-governance.md` and its checker for enforceable architecture;
   - `efg-module-status.md` for lifecycle;
   - `efg-public-api.md` for user-facing imports;
   - focused notes for mathematical rationale;
   - migration/history documents for dated transitions only.

3. Replace duplicated volatile tables with links or generated output where
   practical. Extend an existing script rather than creating a second source
   of truth.

4. Keep the high-level guide short and task-oriented. Provide clear entry
   routes for:

   - new users choosing an import;
   - contributors locating declaration ownership;
   - reviewers checking mathematics/preservation;
   - maintainers changing a facade or lifecycle state; and
   - researchers selecting an open generality task.

5. Remove or rewrite stale snapshot language. Preserve genuinely useful
   historical facts in `docs/HISTORY.md` or migration notes rather than in the
   current architecture contract.

6. Check every local link and every recorded module/declaration name.

## Acceptance criteria

- Each architectural fact has one obvious authoritative home.
- No current document contradicts the deferred-freeze policy or calls the broader
  `Interface.Core` the literal minimal core.
- Volatile counts are generated or checked by governance wherever feasible.
- All links resolve and the design index gives a clear reading order.
- Documentation, knowledge, build, governance, placeholder, and whitespace
  checks pass.
