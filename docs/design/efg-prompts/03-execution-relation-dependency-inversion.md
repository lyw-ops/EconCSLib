# Prompt 03 — Invert Execution/Relation Dependencies

You are working in the EconCSLib repository. Remove reverse dependencies in
which neutral execution helpers import relation/morphism owners.

## Current carrier scope

Read `docs/design/efg-minimal-core-freeze.md`. No repository-wide carrier
freeze is active, but this dependency-inversion task does not modify the three
carrier declarations or the `Interface.StructuralCore` boundary.

## Problem

At least these edges need review:

- `Execution.DependentFiber` imports `Relations.Discrete.Morphism`;
- `Execution.StochasticNaturality` imports
  `Relations.Discrete.Morphism`.

The first module is mostly generic dependent-equivalence calculus. The second
states naturality under an Arena isomorphism. Placing relation ownership below
execution makes otherwise neutral execution closures pull in a higher semantic
layer.

## Required work

1. Generate the exact direct and transitive consumer graph for the two modules
   and for the `Arena.Hom`/`Arena.Iso` declarations they use.

2. Separate three responsibilities:

   - generic dependent-fiber equivalence helpers;
   - structural Arena morphism/isomorphism data; and
   - execution naturality theorems under those relations.

3. Place each responsibility in the lowest honest reusable layer. Acceptable
   outcomes include a neutral Foundation/Math helper, a granular structural
   relation owner outside `StructuralCore`, and a relation-side naturality
   theorem. Do not move morphism data into one of the five structural modules.

4. Migrate all imports and declaration references. Preserve theorem names
   only when ownership remains honest; otherwise perform a documented
   pre-stability hard migration after a zero-consumer/consumer-update audit.

5. Tighten governance with exact negative edges or closure checks so neutral
   execution modules cannot regain relation, equilibrium, simulation, or
   compiler dependencies.

6. Re-measure every affected facade closure and update recorded counts and
   import-boundary examples.

## Acceptance criteria

- The generic dependent-fiber helper imports no game-theory relation module.
- Basic stochastic execution imports no morphism module solely to host a
  naturality theorem.
- Relations may depend on structural/execution semantics, but the inverse edge
  is absent unless a precise lower-level abstraction justifies it.
- No duplicate `Hom`/`Iso` hierarchy is introduced.
- All strict preservation theorems still quantify the same structure and
  prove the same commuting equations.
- Full builds, fresh all-module build, placeholder check, governance, and
  `git diff --check` pass.
