/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.GameForm.IndexedContinuation
import EconCSLib.GameTheory.ExtensiveGame.Observed.ControlledInfrastructure.Subgame

/-!
# Payoff-free observed continuation semantics

Adapter from a `ControlledObservedGame` to an arbitrary indexed continuation
evaluator.

A client supplies strategy spaces, a horizon/index type, an outcome type, and
an evaluator on complete-history roots. The game supplies only payoff-free
dynamics, information, and the history-root type. Root presentation,
lawful-subgame coverage, utility interpretation, and deviation coverage remain
explicit and orthogonal.

`ContinuationSemantics.isStandardSubgamePerfectAt_iff_of_surjective` is the
generic standard-SPE preservation theorem. It assumes complete lawful source
and target systems, exact continuation outcome transport, utility
compatibility, target strategy/deviation coverage, and target lawful-root
coverage. It does not assume that an evaluator is computable, discrete,
bounded, measure-valued, terminating, or derived from state payoffs.
-/

namespace ExtensiveGame.ControlledObservedGame

universe uN uStrategy uHorizon uOutcome uV

variable {N : Type uN}

/-- An arbitrary indexed continuation evaluator attached to a payoff-free
controlled observed EFG. -/
structure ContinuationSemantics (G : ControlledObservedGame N) where
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

variable {G : ControlledObservedGame N}

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

/-- The indexed continuation adapter on an explicit root presentation. -/
def toIndexedGameFormOnPresentation
    (S : G.ContinuationSemantics)
    (roots : G.ContinuationRootPresentation) :
    IndexedContinuationGameForm N :=
  S.toIndexedGameFormOn roots.IsRoot

@[simp]
theorem toIndexedGameFormOnPresentation_outcome
    (S : G.ContinuationSemantics)
    (roots : G.ContinuationRootPresentation)
    (horizon : S.Horizon)
    (root : G.base.toArena.HistoryFrom G.base.init)
    (profile : S.Profile) :
    (S.toIndexedGameFormOnPresentation roots).outcome
        horizon root profile =
      S.evaluate horizon root profile :=
  rfl

/-- Nash equilibrium of an attached evaluator on every root selected by an
explicit root presentation at one semantic index. -/
def IsNashOnPresentationAt
    {V : Type uV} [DecidableEq N] [Preorder V]
    (S : G.ContinuationSemantics)
    (roots : G.ContinuationRootPresentation)
    (utility :
      G.base.toArena.HistoryFrom G.base.init →
        S.Outcome → N → V)
    (horizon : S.Horizon) (profile : S.Profile) : Prop :=
  (S.toIndexedGameFormOnPresentation roots).IsNashOnRootsAt
    utility horizon profile

/-- Subgame perfection of an attached evaluator at one semantic index on an
explicit, possibly conservative, lawful subgame system. -/
def IsSubgamePerfectOnAt
    {V : Type uV} [DecidableEq N] [Preorder V]
    (S : G.ContinuationSemantics)
    (system : G.SubgameSystem)
    (utility :
      G.base.toArena.HistoryFrom G.base.init →
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
      G.base.toArena.HistoryFrom G.base.init →
        S.Outcome → N → V)
    (horizon : S.Horizon) (profile : S.Profile) : Prop :=
  S.IsSubgamePerfectOnAt system.toSubgameSystem
    utility horizon profile

/-- The explicit-presentation adapter introduces no new equilibrium
predicate. -/
theorem isNashOnPresentationAt_iff
    {V : Type uV} [DecidableEq N] [Preorder V]
    (S : G.ContinuationSemantics)
    (roots : G.ContinuationRootPresentation)
    (utility :
      G.base.toArena.HistoryFrom G.base.init →
        S.Outcome → N → V)
    (horizon : S.Horizon) (profile : S.Profile) :
    S.IsNashOnPresentationAt roots utility horizon profile ↔
      (S.toIndexedGameFormOnPresentation roots).IsNashOnRootsAt
        utility horizon profile :=
  Iff.rfl

/-- An assumption-explicit indexed continuation morphism preserves and
reflects standard SPE.

The two `CompleteSubgameSystem`s certify that the tested roots are exactly the
structurally lawful roots of their respective payoff-free observed EFGs. The
morphism field `map_outcome` preserves every continuation outcome for every
profile; `StrategySurjective` supplies reverse coverage of target deviations;
and `DeclaredRootSurjective` supplies reverse coverage of lawful target roots.
`UtilityCompatible` states the final outcome interpretation square. No
compiler or weak serialization receives these properties automatically. -/
theorem isStandardSubgamePerfectAt_iff_of_surjective
    {H : ControlledObservedGame N}
    {V : Type uV} [DecidableEq N] [Preorder V]
    (S : G.ContinuationSemantics)
    (T : H.ContinuationSemantics)
    (sourceSystem : G.CompleteSubgameSystem)
    (targetSystem : H.CompleteSubgameSystem)
    (f :
      (S.toIndexedGameFormOn
        sourceSystem.toSubgameSystem.IsRoot).Hom
        (T.toIndexedGameFormOn
          targetSystem.toSubgameSystem.IsRoot))
    (sourceUtility :
      S.Horizon →
        G.base.toArena.HistoryFrom G.base.init →
          S.Outcome → N → V)
    (targetUtility :
      T.Horizon →
        H.base.toArena.HistoryFrom H.base.init →
          T.Outcome → N → V)
    (hutility :
      f.UtilityCompatible sourceUtility targetUtility)
    (hstrategy : f.StrategySurjective)
    (hroot : f.DeclaredRootSurjective)
    (horizon : S.Horizon)
    (profile : S.Profile) :
    S.IsStandardSubgamePerfectAt sourceSystem
        (sourceUtility horizon) horizon profile ↔
      T.IsStandardSubgamePerfectAt targetSystem
        (targetUtility (f.horizonMap horizon))
        (f.horizonMap horizon) (f.mapProfile profile) := by
  exact
    f.isNashOnRootsAt_iff_of_surjective
      hutility hstrategy hroot horizon profile

end ContinuationSemantics

end ExtensiveGame.ControlledObservedGame
