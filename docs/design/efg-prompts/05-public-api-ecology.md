# Prompt 05 — Improve the Public API Ecology

You are working in the EconCSLib repository. Reduce navigation and accidental
coupling costs in the EFG public surface without creating compatibility noise.

## Current carrier scope

Read `docs/design/efg-minimal-core-freeze.md`. No repository-wide carrier
freeze is active, but this API-ecology task does not change the three carrier
declarations or the current `Interface.StructuralCore` boundary.

## Problem

The architecture has granular facades, but the overall surface is still large.
Lean exposes every transitive declaration, lifecycle status is module-level,
and users can struggle to identify which declarations are stable entry points
versus implementation details. Reuse suffers if each client imports the
largest facade or discovers APIs by accidental transitive visibility.

## Required work

1. Run the declaration-usage report and build an evidence table for every
   canonical facade:

   - direct imports;
   - transitive EFG/local closure;
   - documented positive declarations;
   - accidental transitive declarations;
   - repository consumers; and
   - overlap with adjacent facades.

2. Interview the repository itself: inspect examples and downstream modules to
   identify concrete import personas (structural modeler, finite executor,
   objective author, discrete equilibrium user, analytic kernel user,
   compiler author).

3. For each facade, decide one of:

   - keep exact responsibility;
   - narrow imports;
   - split into independently useful granular facades;
   - merge only when two facades have indistinguishable real consumers; or
   - demote an import path from recommended navigation without deleting valid
     declarations.

4. Do not add facade aliases or forwarding modules for hypothetical users.
   Do not make `EconCSLib.lean` broad. Do not equate name-resolvability with a
   stability promise.

5. Add positive `#check` evidence for each promised facade declaration and
   negative guards or exact closure checks for important exclusions.

6. Update `efg-public-api.md` into a task-oriented import guide. Ensure every
   recommended declaration has exactly one obvious smallest facade.

7. Update lifecycle rows, migration notes, closure counts, and governance in
   the same change.

## Acceptance criteria

- Every facade has a distinct, one-sentence user need backed by actual
  declarations.
- No two recommended facades are pure synonyms.
- Root and StructuralCore closures do not grow.
- At least one measured navigation or closure improvement is achieved, unless
  the evidence proves the current surface locally minimal; in that case
  record the no-op analysis instead of forcing churn.
- The unexplained public endpoint baseline does not grow.
- All import regressions, builds, governance, placeholder, and whitespace
  checks pass.
