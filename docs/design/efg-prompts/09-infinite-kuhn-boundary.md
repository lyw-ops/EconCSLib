# Prompt 09 — Formalize the Infinite-Kuhn Boundary

You are working in the EconCSLib repository. Determine and formalize the
strongest correct Kuhn-style equivalence beyond the current finite setting.

## Current carrier scope

Read `docs/design/efg-minimal-core-freeze.md`. No repository-wide carrier
freeze is active, but this theorem-boundary task does not modify carriers or
`Interface.StructuralCore`. Extra recall, measurability, termination,
topological, and conditioning hypotheses must remain external.

## Problem

Finite perfect-recall Kuhn equivalence does not automatically extend to
infinite horizon, infinitely many information states, uncountable actions, or
arbitrary measures. The library needs an explicit theorem boundary rather than
an aspirational unrestricted name.

## Required work

1. Review authoritative literature and produce a hypothesis matrix covering:

   - finite versus countable/infinite histories;
   - finite, countable, and standard-Borel action spaces;
   - behavioral versus mixed/general strategies;
   - perfect recall/no absent-mindedness;
   - termination or infinite plays;
   - conditional distributions and zero-probability information sets; and
   - realization equivalence at terminal outcomes versus complete path laws.

2. Map each hypothesis to an existing Lean certificate or identify the
   smallest missing downstream certificate.

3. Select one theorem with a complete proof route supported by current
   Mathlib. State it in a design/knowledge node before implementation. Prefer a
   useful restricted infinite theorem over an unprovable maximal claim.

4. Implement the prerequisite probability lemmas in `Math/` only when they are
   game-independent. Keep EFG-specific assembly in the observed execution or
   equilibrium layer.

5. Prove both directions only if both are mathematically valid. Otherwise name
   a one-way realization theorem directionally.

6. Show specialization to the existing finite Kuhn theorem and add an example
   that genuinely lies outside the old finite hypothesis package.

## Stop conditions

If the proof requires an unavailable regular conditional probability,
infinite product-measure, measurable-selection, or standard-Borel result,
record the exact missing lemma and a source-backed proof plan in
`docs/knowledge/staged/`. Do not introduce an axiom, placeholder theorem, or
weakened statement under the old name.

## Acceptance criteria

- The scope boundary is source-backed and explicit.
- The Lean theorem name advertises its finite/countable/analytic strength.
- Recall and conditioning assumptions are neither hidden nor bundled with
  unrelated finiteness.
- Existing finite semantics is recovered by a proved specialization.
- All applicable Lean, knowledge, governance, placeholder, and whitespace
  checks pass.
