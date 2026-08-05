# Draft EFG Stabilization Prompt Pack

This directory contains self-contained prompts for resolving the issues found
while reviewing the EFG minimal core. The pack remains draft until that review
finishes; no repository-wide minimal-core compatibility freeze is active.
Before dispatching a prompt, reconcile it with
[`../efg-minimal-core-freeze.md`](../efg-minimal-core-freeze.md).

## Shared scope

These follow-up prompts are currently scoped away from changing:

- `Arena`;
- `ControlledGame`;
- `ControlledObservedGame`; or
- the exact five-module closure of `Interface.StructuralCore`.

This is task scoping, not a claim that the declarations are frozen. If a task
finds a concrete representation failure that requires changing them, stop
implementation and return an evidence-backed carrier proposal for the ongoing
review. New semantics should otherwise live in certificates, adapters,
relations, execution layers, or compilers.

## Task map

| Prompt | Problem addressed | Kind | Recommended order |
|---|---|---|---:|
| [`01-carrier-ownership-convergence.md`](01-carrier-ownership-convergence.md) | payoff-free and payoff-aware APIs still expose parallel ownership surfaces | architecture/migration | 1 |
| [`02-objective-parametric-pure-spe.md`](02-objective-parametric-pure-spe.md) | history/path objectives are not yet the canonical total pure standard-SPE route | semantics/theorem API | 2 |
| [`03-execution-relation-dependency-inversion.md`](03-execution-relation-dependency-inversion.md) | neutral execution helpers import relation/morphism owners | dependency architecture | 1 |
| [`04-reachability-history-bridge.md`](04-reachability-history-bridge.md) | reachability and typed-history witnesses lack a complete public bridge | reusable mathematics | 1 |
| [`05-public-api-ecology.md`](05-public-api-ecology.md) | large facade surface and accidental transitive visibility reduce discoverability | ecosystem/API | 3 |
| [`06-mathematical-provenance.md`](06-mathematical-provenance.md) | mathematical ownership is better documented than literature provenance | documentation/math review | 2 |
| [`07-documentation-consolidation.md`](07-documentation-consolidation.md) | overlapping architecture notes can drift and obscure authority | documentation/tooling | 4 |
| [`08-arbitrary-measure-general-strategies.md`](08-arbitrary-measure-general-strategies.md) | “general strategy” currently stops at discrete/countable laws | research implementation | after 1–7 |
| [`09-infinite-kuhn-boundary.md`](09-infinite-kuhn-boundary.md) | finite Kuhn results do not justify an unrestricted infinite theorem | research/formalization | after 1–7 |
| [`10-sequential-equilibrium-foundation.md`](10-sequential-equilibrium-foundation.md) | beliefs, assessments, consistency, and sequential rationality are absent | research/formalization | after 1–7 |
| [`11-determinacy-scope.md`](11-determinacy-scope.md) | finite constructive and infinite descriptive-set-theoretic determinacy need an explicit boundary | research/formalization | after 1–7 |

Prompts 01, 03, 04, and 06 are separable in mathematical intent, but they may
touch shared governance and public-API documents. Run them in separate
worktrees or serialize their final documentation edits. Prompt 05 should use
the post-migration declaration graph. Prompt 07 is the final consolidation
pass.

## Completion standard

Every implementation task must:

1. inspect the complete dirty worktree and preserve unrelated changes;
2. read `AGENTS.md`, `README.md`, `docs/design.md`, the freeze-readiness note, and
   the task-specific neighboring modules;
3. search Mathlib and current repository declarations before adding an
   abstraction;
4. keep `EconCSLib/` free of ordinary `sorry` and `admit`;
5. add positive and negative import regressions when a facade boundary
   changes;
6. synchronize lifecycle, governance, public API, migration, and audit
   documents only where the task actually changes their claims; and
7. run at least:

   ```bash
   lake build
   lake build EconCSLib.Examples
   python3 scripts/build_efg_modules.py
   python3 scripts/check_lean_placeholders.py EconCSLib
   python3 scripts/check_efg_governance.py
   git diff --check
   ```

Research prompts have an additional stop rule: if the intended theorem is
false or requires unresolved hypotheses, record the exact gap in
`docs/knowledge/staged/` or a design note. Do not reserve an API with a
placeholder theorem and do not weaken the statement silently.
