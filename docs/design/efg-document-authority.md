# EFG documentation authority and claim inventory

This note is the navigation contract for EFG documentation. It does not
override Lean or restate volatile module tables. When two documents appear to
disagree, use this authority order:

1. Lean source for declarations and proofs.
2. [`efg-minimal-core-freeze.md`](efg-minimal-core-freeze.md) for API-growth
   policy, freeze readiness, and the active carrier regressions.
3. [`efg-governance.md`](efg-governance.md) and
   `scripts/check_efg_governance.py` for enforceable architecture and facade
   closures.
4. [`efg-module-status.md`](efg-module-status.md) for module lifecycle.
5. [`efg-public-api.md`](efg-public-api.md) for user-facing imports.
6. Focused notes for mathematical rationale and theorem boundaries.
7. Migration and history documents for dated transitions only.

## Claim inventory

| Document | Claim class | Authority |
|---|---|---|
| `docs/design.md` EFG row | project-level summary | Links to this inventory; owns no EFG detail |
| `efg-document-authority.md` | authority order, claim inventory and task routes | Authoritative documentation navigation contract |
| [`extensive_game.md`](extensive_game.md) | task-oriented architecture overview | Lean for declarations; the focused authorities above for policy |
| [`efg-minimal-core-freeze.md`](efg-minimal-core-freeze.md) | API-growth policy, freeze readiness, candidate carrier boundary, active carrier regressions | Authoritative for freeze state |
| [`efg-governance.md`](efg-governance.md) | dependency direction, exact facade closures, placement and root policy | Authoritative with its checker |
| [`efg-module-status.md`](efg-module-status.md) | complete module census, lifecycle, responsibility and recommended facade | Authoritative lifecycle register; checker verifies source parity and totals |
| [`efg-public-api.md`](efg-public-api.md) | import choice and the semantics promised by each facade | Authoritative user import guide; closure counts are links to governance |
| [`efg-controlled-api.md`](efg-controlled-api.md) | controlled hierarchy navigation and responsibility rationale | Focused ownership guide; Lean and governance decide actual owners/edges |
| [`efg-preservation-matrix.md`](efg-preservation-matrix.md) | relation strengths and proved preservation coverage | Focused mathematical review ledger; Lean decides proof status |
| [`efg-mathematical-provenance.md`](efg-mathematical-provenance.md) | literature-to-Lean hypothesis translation and gaps | Focused provenance ledger |
| [`efg-arbitrary-measure-strategies.md`](efg-arbitrary-measure-strategies.md) | arbitrary-measure strategy carrier boundary | Focused mathematical rationale |
| [`efg-infinite-kuhn-boundary.md`](efg-infinite-kuhn-boundary.md) | finite-history versus infinite-path Kuhn boundary | Focused mathematical rationale |
| [`efg-sequential-equilibrium-foundation.md`](efg-sequential-equilibrium-foundation.md) | experimental assessment/consistency boundary and promotion gaps | Focused mathematical rationale |
| [`efg-determinacy-scope.md`](efg-determinacy-scope.md) | logical, well-founded, topological and stochastic determinacy scopes | Focused mathematical rationale |
| [`efg-representation-compilation.md`](efg-representation-compilation.md) | frontend choice and compiler preservation boundary | Focused representation guide |
| [`efg-general-foundations.md`](efg-general-foundations.md) and numbered continuations | long-form rationale, proposed generality and theorem roadmap | Focused design/roadmap; not lifecycle or proof authority |
| [`efg-import-granularity.md`](efg-import-granularity.md) | dependency-split rationale and before/after audit | Migration audit; current closures live in governance |
| [`efg-api-migration.md`](efg-api-migration.md) | completed path/name transitions and downstream recipes | Migration history only |
| [`efg-minimal-core-structure-audit.md`](efg-minimal-core-structure-audit.md) | findings that motivated the current architecture | Historical audit; live state is delegated to freeze, governance and lifecycle authorities |
| [`efg-prompts/README.md`](efg-prompts/README.md) and its prompt files | implementation work orders and acceptance criteria | Planning/history, never evidence that a theorem exists |

The constructor audit in
[`observed-game-constructors.md`](observed-game-constructors.md) and the API
reference continuation in
[`extensive_game-2-reference.md`](extensive_game-2-reference.md) are adjacent
focused notes rather than `efg-*.md` files; the same authority order applies.

## Repeated-claim routing

| Repeated claim | Single current home | Other documents should do this |
|---|---|---|
| API growth or carrier compatibility is frozen or deferred | `efg-minimal-core-freeze.md` | Link to the decision; do not infer source compatibility from “Canonical” or from the growth freeze |
| Exact facade/root closure counts | `efg-governance.md` plus checker constants | Link to the governed table; do not copy it |
| Number and lifecycle of modules | `efg-module-status.md` plus checker source-parity check | Link to the register; do not copy its status totals |
| Which import a user should choose | `efg-public-api.md` | Link to the relevant row |
| Which module owns a declaration | Lean source; module status summarizes responsibility | Link to the source/module row |
| Preservation strength | Lean theorem plus `efg-preservation-matrix.md` | Never upgrade a missing field by prose |
| Literature interpretation | `efg-mathematical-provenance.md` and focused notes | Record representation translations and gaps explicitly |
| Removed or renamed APIs | `efg-api-migration.md` or `docs/HISTORY.md` | Do not present dated transitions as current architecture |

## Task routes

- New user choosing an import: read
  [`efg-public-api.md`](efg-public-api.md).
- Contributor locating ownership: consult
  [`efg-module-status.md`](efg-module-status.md), then the defining Lean
  module; for the controlled family also use
  [`efg-controlled-api.md`](efg-controlled-api.md).
- Reviewer checking mathematics: start with
  [`efg-mathematical-provenance.md`](efg-mathematical-provenance.md) and
  [`efg-preservation-matrix.md`](efg-preservation-matrix.md), then inspect the
  cited Lean declarations.
- Maintainer changing a facade or lifecycle state: read
  [`efg-minimal-core-freeze.md`](efg-minimal-core-freeze.md),
  [`efg-governance.md`](efg-governance.md), and
  [`efg-module-status.md`](efg-module-status.md), then run the governance and
  full module checks.
- Researcher selecting an open generality task: use
  [`efg-general-foundations-4-theorem-roadmap.md`](efg-general-foundations-4-theorem-roadmap.md),
  the focused boundary notes, and the staged nodes under
  `docs/knowledge/staged/extensive_game/`. A roadmap entry is not a formal
  theorem until the cited Lean declaration exists.
