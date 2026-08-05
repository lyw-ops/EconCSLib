# Prompt 01 — Converge Carrier and Adapter Ownership

You are working in the EconCSLib repository. Resolve the remaining parallel
ownership between the canonical payoff-free observed EFG and the downstream
payoff-aware/discrete compatibility surfaces.

## Current carrier scope

Read `docs/design/efg-minimal-core-freeze.md`. No repository-wide carrier
freeze is active, but this task is scoped to ownership and adapters. Do not
modify the three carrier declarations or `Interface.StructuralCore`; report
any evidence that such a change is necessary back to the core review.

## Problem

`ControlledObservedGame` is the canonical information carrier, but
`ObservedGame`, `ObservedChanceGame`, `Observed.Behavior`, and
`Observed.Controlled.Compat.*` still expose a large parallel vocabulary.
Some duplication is a legitimate payoff or PMF adapter; some may be duplicate
theorem ownership that makes discovery and reuse harder.

## Required work

1. Inspect the complete worktree and produce a declaration/consumer inventory
   for:

   - `Observed/Controlled.lean` and all `Observed/Controlled/**` modules;
   - `Observed/Game.lean`, `Observed/Chance.lean`, `Observed/Behavior.lean`;
   - all `Observed/Controlled/Compat/**` modules; and
   - facade/example consumers of both spellings.

2. Classify each parallel declaration as one of:

   - canonical payoff-free owner;
   - necessary state-payoff adapter;
   - necessary discrete chance-law adapter;
   - namespace compatibility spelling;
   - genuinely different semantics; or
   - redundant ownership.

3. Move representation-independent definitions and theorems to the existing
   payoff-free owner namespace. Keep payoff-aware declarations only when their
   statement actually mentions payoff data or the payoff-aware carrier.
   Keep PMF-specific declarations in a discrete law/adapter layer.

4. Prefer definitional projections and thin `abbrev`/theorem adapters over
   rebuilding observation, information, strategy, recall, morphism, or subgame
   structures.

5. Migrate repository consumers to the canonical owner. Delete a redundant
   compatibility declaration only after showing zero source consumers and
   recording the honest replacement. Do not claim equivalence when strategy
   spaces, roots, deviation quantifiers, chance laws, or payoff semantics
   differ.

6. Add or tighten governance so canonical payoff-free modules cannot regain a
   downstream payoff-aware dependency.

7. Update `efg-controlled-api.md`, `efg-public-api.md`,
   `efg-api-migration.md`, `efg-module-status.md`, and the structural audit
   only to reflect real changes.

## Acceptance criteria

- There is one documented authoritative owner for every shared mathematical
  concept.
- The payoff-aware and chance layers are visibly additive adapters, not rival
  foundational carriers.
- Canonical payoff-free imports reach no `ObservedGame`,
  `ObservedChanceGame`, or `.Compat` module.
- Existing constructors have round-trip simp lemmas where the round trip is
  definitionally or propositionally valid.
- The declaration-usage report shows no newly unexplained public endpoints.
- Relevant focused builds, full builds, placeholder checks, governance, and
  `git diff --check` pass.

If the inventory proves that a suspected duplication is already only a thin
adapter, do not churn the API. Record the evidence and close that item as a
verified no-op.
