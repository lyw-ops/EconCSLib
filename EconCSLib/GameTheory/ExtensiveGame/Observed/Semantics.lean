/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.GameForm.IndexedContinuation
import EconCSLib.GameTheory.ExtensiveGame.Observed.Game

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.Semantics

Adapter from an observed EFG to an arbitrary indexed continuation evaluator.

The operational modules provide concrete deterministic and discrete-PMF
evaluators. `ContinuationSemantics` is the extension boundary for other
semantics: a client supplies its strategy spaces, horizon/index type, outcome
type, and evaluator on complete history roots. The observed game supplies the
root type and presentation-designated predicate exactly once.

Converting with `toIndexedGameForm` reuses
`IndexedContinuationGameForm` morphisms and Nash-on-declared-roots transfer.
The default adapter uses presentation-designated roots. Equilibrium on a
possibly conservative lawful system uses `IsSubgamePerfectOnAt`; complete
standard SPE uses `IsStandardSubgamePerfectAt` with a
`CompleteSubgameSystem`. This adapter does not
assume that the evaluator is computable, discrete, bounded, or measure-valued,
and it does not assert application-specific convergence or termination
theorems.
-/

namespace ExtensiveGame.ObservedGame

universe uN uU uStrategy uHorizon uOutcome uV

variable {N : Type uN} {U : Type uU}

/-- An arbitrary indexed continuation evaluator attached to an observed EFG. -/
structure ContinuationSemantics (G : ObservedGame N U) where
  /-- Complete strategy space for each player in this semantic mode. -/
  Strategy : N → Type uStrategy
  /-- Horizon, approximation, discount, or total-semantics index. -/
  Horizon : Type uHorizon
  /-- Result type of evaluation. -/
  Outcome : Type uOutcome
  /-- Evaluate a complete profile from a complete history root. -/
  evaluate :
    Horizon →
      G.base.toArena.HistoryFrom G.base.init →
      (∀ i, Strategy i) → Outcome

namespace ContinuationSemantics

variable {G : ObservedGame N U}

/-- Complete profiles of one attached continuation semantics. -/
abbrev Profile (S : G.ContinuationSemantics) :=
  ∀ i, S.Strategy i

/-- Reuse the generic indexed continuation layer with an explicit tested-root
predicate. -/
def toIndexedGameFormOn
    (S : G.ContinuationSemantics)
    (roots :
      G.base.toArena.HistoryFrom G.base.init → Prop) :
    IndexedContinuationGameForm N where
  Strategy := S.Strategy
  Horizon := S.Horizon
  Root := G.base.toArena.HistoryFrom G.base.init
  IsDeclaredRoot := roots
  Outcome := S.Outcome
  outcome := S.evaluate

/-- The indexed continuation adapter on presentation-designated roots. -/
def toIndexedGameForm (S : G.ContinuationSemantics) :
    IndexedContinuationGameForm N :=
  S.toIndexedGameFormOn G.IsDesignatedContinuationRoot

@[simp]
theorem toIndexedGameForm_outcome
    (S : G.ContinuationSemantics)
    (horizon : S.Horizon)
    (root : G.base.toArena.HistoryFrom G.base.init)
    (profile : S.Profile) :
    S.toIndexedGameForm.outcome horizon root profile =
      S.evaluate horizon root profile :=
  rfl

/-- Nash equilibrium of an attached evaluator on every
presentation-designated continuation at one semantic index. -/
def IsNashOnDesignatedContinuationsAt
    {V : Type uV} [DecidableEq N] [Preorder V]
    (S : G.ContinuationSemantics)
    (utility :
      (G.base.toArena.HistoryFrom G.base.init) →
        S.Outcome → N → V)
    (horizon : S.Horizon) (profile : S.Profile) : Prop :=
  S.toIndexedGameForm.IsNashOnRootsAt
    utility horizon profile

/-- Subgame perfection of an attached evaluator at one semantic index on an
explicit, possibly conservative, lawful subgame system. -/
def IsSubgamePerfectOnAt
    {V : Type uV} [DecidableEq N] [Preorder V]
    (S : G.ContinuationSemantics)
    (system : G.SubgameSystem)
    (utility :
      (G.base.toArena.HistoryFrom G.base.init) →
        S.Outcome → N → V)
    (horizon : S.Horizon) (profile : S.Profile) : Prop :=
  (S.toIndexedGameFormOn system.IsRoot).IsNashOnRootsAt
    utility horizon profile

/-- Standard SPE of an attached evaluator at one semantic index on every
structurally lawful subgame root. -/
def IsStandardSubgamePerfectAt
    {V : Type uV} [DecidableEq N] [Preorder V]
    (S : G.ContinuationSemantics)
    (system : G.CompleteSubgameSystem)
    (utility :
      (G.base.toArena.HistoryFrom G.base.init) →
        S.Outcome → N → V)
    (horizon : S.Horizon) (profile : S.Profile) : Prop :=
  S.IsSubgamePerfectOnAt system.toSubgameSystem
    utility horizon profile

/-- The designated-root adapter introduces no new equilibrium predicate. -/
theorem isNashOnDesignatedContinuationsAt_iff
    {V : Type uV} [DecidableEq N] [Preorder V]
    (S : G.ContinuationSemantics)
    (utility :
      (G.base.toArena.HistoryFrom G.base.init) →
        S.Outcome → N → V)
    (horizon : S.Horizon) (profile : S.Profile) :
    S.IsNashOnDesignatedContinuationsAt utility horizon profile ↔
      S.toIndexedGameForm.IsNashOnRootsAt
        utility horizon profile :=
  Iff.rfl

end ContinuationSemantics

end ExtensiveGame.ObservedGame
