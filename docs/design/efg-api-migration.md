# EFG Downstream Migration

This note records the source-level changes made while converging the EFG
public facade. No theorem or mathematical construction was deleted; the main
compatibility impact is that a few clients must add a narrower explicit import
or update pre-release record-field labels.

## Import migration

| Former dependency | Required import now |
|---|---|
| occurrence-sensitive `GameTree` compiler obtained from `import EconCSLib` | `import EconCSLib.GameTheory.ExtensiveGame.Interface.Compilation.Discrete` |
| bounded deterministic, observed behavioral, or PMF-kernel execution obtained from `Interface.Execution.Discrete` | `Interface.Execution.Finite` avoids infinite path measures; the old import remains valid |
| infinite discrete `Arena.pathLaw`, almost-sure termination, or payoff convergence | `Interface.Execution.Infinite`; the old `Interface.Execution.Discrete` import remains valid |
| measurable-kernel execution obtained transitively | `Interface.Execution.Analytic` |
| strict representation morphisms, information refinements, PMF couplings, or weak simulations | `Interface.Relations.Discrete` |
| bounded pure/behavioral/mixed Nash, termination, or finite Kuhn transfer | `Interface.Equilibrium.Discrete` |
| measurable path utility, constructive kernel Nash, absolute-prefix continuation, or conditioning | `Interface.Equilibrium.Analytic` |
| fresh-clock restart declarations | `Interface.Restart` |
| finite observed-EFG compilers or PMF FOSG serialization | `Interface.Compilation.Discrete` |
| both restart and compiler branches from one legacy import | `Interface.SimulationFramework` (compatibility-only) |

The root aggregate exports finite/PMF execution and the standalone finite
`GameTree`/backward-induction and exact zero-sum chance-tree tracks. Infinite
discrete paths, historical endpoint-policy equilibrium, Arena extraction,
Zermelo, and the observed-EFG reference compilers now require explicit
imports.

No source edit is required merely because a caller already imports
`Interface.Execution.Discrete`, `Interface.Relations`,
`Interface.Equilibrium`, or `Interface.Compilation`: those paths retain their
former declaration closures as supported compatibility aggregates. Switching
to a new granular path is an opt-in dependency reduction. The facade split
moved no declaration and changed no theorem name, namespace, or record field.

## Record-field migration

The following pre-release field labels were semantically too strong. Update
named record literals as follows:

| Structure family | Old field | Current field |
|---|---|---|
| `ContinuationGameForm`, `IndexedContinuationGameForm` | `IsSubgameRoot` | `IsDeclaredRoot` |
| their `Hom`, `Iso`, and relation structures | `map_subgameRoot` | `map_declaredRoot` |
| their root-coverage predicates | `SubgameRootSurjective`, `SubgameRootReflecting` | `DeclaredRootSurjective`, `DeclaredRootReflecting` |
| `ObservedGame` | `IsSubgameRoot` | `IsDesignatedContinuationRoot` |
| observed isomorphism/refinement structures | `map_subgameRoot` | `map_designatedContinuationRoot` |

For example:

```lean
-- before
{ Strategy := Strategy
  Root := Root
  IsSubgameRoot := roots
  Outcome := Outcome
  outcome := outcome }

-- now
{ Strategy := Strategy
  Root := Root
  IsDeclaredRoot := roots
  Outcome := Outcome
  outcome := outcome }
```

and an observed presentation now uses:

```lean
{ base := base
  -- observation and information fields omitted
  IsDesignatedContinuationRoot := roots
  init_isDesignatedContinuationRoot := init_mem }
```

The field types and positional constructor argument order did not change for
these label-only renames. Named record literals must still be edited. Lean can
alias an ordinary declaration or projection, but an alias cannot make an old
field label legal inside a record literal, so a source-compatible deprecation
alias is not possible.

## `SubgameSystem` literals

`ObservedGame.SubgameSystem` separates selection from structural lawfulness.
Construct it with exactly:

```lean
{ IsRoot := roots
  init_isRoot := init_mem
  lawful := by
    intro root hroot
    exact
      { root_information_singleton := by
          -- prove the proper-root singleton condition
          ...
        information_closed := by
          -- prove information-set closure after the root
          ... } }
```

`root_information_singleton` and `information_closed` remain derived
accessors on a completed `SubgameSystem`. Presentation designation is not a
field; prove `SubgameSystem.IsPresentationVisible` separately when needed.
Use `CompleteSubgameSystem` only when the selected roots cover every
`IsLawfulSubgameRoot`.

## Solution-concept names

The old `IsSPEForPayoff` and unqualified `Is...SubgamePerfect` spellings were
not retained. Choose the name that states the actual root scope:

- `IsNashOnDesignatedContinuations...` for presentation-selected roots;
- `Is...SubgamePerfectOn ... system` for one explicit lawful system; or
- `Is...StandardSubgamePerfect ... completeSystem` for coverage of every
  structurally lawful root.

A caller-declared or presentation-designated root predicate is not, by itself,
a standard-subgame certificate. Compatibility aliases with the former names
would preserve the misleading claim, so this migration is intentionally
explicit rather than a bulk rename or silent alias.

## Declaration deprecations

The finite imperfect-information frontend has one exact declaration alias:

| Deprecated declaration | Replacement | Since | Semantics |
|---|---|---|---|
| `FiniteImperfectGame.actionAt_same_info_label` | `FiniteImperfectGame.actionAt_same_info` | 2026-07-29 | Identical transport-aware information-consistency statement |

This alias is eligible for `@[deprecated replacement]` because its theorem
statement is unchanged.  Endpoint versus occurrence strategies, state
re-rooting versus lawful subgames, and designated-root versus complete-system
solution concepts do not receive such aliases: their semantics differ.

## Completed root migration

On 2026-07-30 the root replaced `Interface.Execution.Discrete` with
`Interface.Execution.Finite`. Infinite path laws are available from
`Interface.Execution.Infinite` or the old supported compatibility aggregate.
The historical endpoint `GameTreeSPE`, `GameTreeNE`, and
`GameTreeStrategicForm` modules, the niche `FiniteArenaExtraction` bridge, and
`Zermelo` also became explicit imports.

Existing examples now import the implementation paths they use, and
`RootImportBoundary` checks both the retained finite surface and the removed
transitive names. The granular facade and examples builds are the migration
regressions. No theorem, declaration, namespace, or public module path was
deleted by this root-only dependency change.
