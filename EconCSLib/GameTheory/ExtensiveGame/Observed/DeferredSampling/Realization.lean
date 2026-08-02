/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.DeferredSampling.Execution

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.DeferredSampling.Realization

Behavioral-to-mixed history, payoff, continuation, and Nash on presentation-designated continuations transfer.
-/

namespace ExtensiveGame.ObservedChanceGame

universe uN uU uAS uO uI uP

variable {N : Type uN} {U : Type uU}

/-- Under finite information and no absent-mindedness, independently sampling
a complete pure plan from a behavioral profile gives exactly the same bounded
complete-history law as sampling locally during play. -/
theorem behavioralToMixed_stoppedHistoryLawFrom_of_noAbsentMindedness
    (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)
    [Fintype N] [DecidableEq N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteNoAbsentMindednessHypotheses)
    (profile : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) :
    G.mixedStoppedHistoryLawFrom
        (h.behavioralToMixedProfile profile)
        current fuel =
      G.observed.base.toArena.stochasticHistoryPMFFrom
        (BehavioralProfile.toHistoryPolicy G profile)
        current fuel := by
  classical
  letI (i : N) : Finite (G.observed.InfoState i) :=
    h.finiteInfoState i
  letI (i : N) : Fintype (G.observed.InfoState i) :=
    Fintype.ofFinite (G.observed.InfoState i)
  letI : Fintype G.observed.DecisionKey :=
    inferInstance
  let hnoAbsent :=
    h.noAbsentMindedness
  let tree :=
    G.boundedHistoryTree
      hnoAbsent current Finset.univ
      (ObservedGame.FutureDecisionKeysAvailable.univ
        current)
      fuel
  calc
    G.mixedStoppedHistoryLawFrom
        (h.behavioralToMixedProfile profile)
        current fuel =
      ((PMF.fintypePi
        (profile.decisionLaw G.observed)).map
          G.observed.decisionTableEquiv).bind
        (fun pureProfile =>
          G.observed.base.toArena.stochasticHistoryPMFFrom
            (BehavioralProfile.toHistoryPolicy G
              (pureProfile.toBehavioral G.observed))
            current fuel) := by
      unfold mixedStoppedHistoryLawFrom
      rw [h.map_fintypePi_decisionLaw profile]
    _ = PMF.FreshQueryTree.runPresampled
          (profile.decisionLaw G.observed)
          tree :=
      (G.boundedHistoryTree_runPresampled_eq_flatMixed
        profile hnoAbsent current fuel).symm
    _ = G.observed.base.toArena.stochasticHistoryPMFFrom
          (BehavioralProfile.toHistoryPolicy G profile)
          current fuel :=
      G.boundedHistoryTree_runPresampled
        profile hnoAbsent current fuel

/-- Compatibility wrapper under the stronger traditional finite Kuhn
hypotheses. -/
theorem behavioralToMixed_stoppedHistoryLawFrom
    (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)
    [Fintype N] [DecidableEq N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (profile : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) :
    G.mixedStoppedHistoryLawFrom
        (h.behavioralToMixedProfile profile)
        current fuel =
      G.observed.base.toArena.stochasticHistoryPMFFrom
        (BehavioralProfile.toHistoryPolicy G profile)
        current fuel := by
  let hweak :=
    h.toFiniteNoAbsentMindednessHypotheses
  simpa [hweak,
    ObservedGame.FiniteNoAbsentMindednessHypotheses.behavioralToMixedProfile,
    ObservedGame.FiniteNoAbsentMindednessHypotheses.behavioralToMixedStrategy,
    ObservedGame.FiniteKuhnHypotheses.behavioralToMixedProfile,
    ObservedGame.FiniteKuhnHypotheses.behavioralToMixedStrategy,
    ObservedGame.FiniteKuhnHypotheses.toFiniteNoAbsentMindednessHypotheses] using
      G.behavioralToMixed_stoppedHistoryLawFrom_of_noAbsentMindedness
        hweak profile current fuel

/-- Behavioral-to-mixed conversion preserves the complete bounded optional
payoff law at every continuation root under finite information and no
absent-mindedness. -/
theorem behavioralToMixed_stoppedPayoffLawFrom_of_noAbsentMindedness
    (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)
    [Fintype N] [DecidableEq N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteNoAbsentMindednessHypotheses)
    (profile : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) :
    G.mixedStoppedPayoffLawFrom
        (h.behavioralToMixedProfile profile)
        current fuel =
      G.behavioralStoppedPayoffLawFrom
        profile current fuel := by
  calc
    G.mixedStoppedPayoffLawFrom
        (h.behavioralToMixedProfile profile)
        current fuel =
      (G.mixedStoppedHistoryLawFrom
        (h.behavioralToMixedProfile profile)
        current fuel).map
          G.stoppedPayoffAtHistory :=
      G.mixedStoppedPayoffLawFrom_eq_map_history
        (h.behavioralToMixedProfile profile)
        current fuel
    _ = (G.observed.base.toArena.stochasticHistoryPMFFrom
            (BehavioralProfile.toHistoryPolicy G profile)
            current fuel).map
          G.stoppedPayoffAtHistory := by
      rw [G.behavioralToMixed_stoppedHistoryLawFrom_of_noAbsentMindedness
        h profile current fuel]
    _ = G.behavioralStoppedPayoffLawFrom
        profile current fuel :=
      rfl

/-- Compatibility wrapper for payoff-law preservation under the stronger
traditional finite Kuhn hypotheses. -/
theorem behavioralToMixed_stoppedPayoffLawFrom
    (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)
    [Fintype N] [DecidableEq N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (profile : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) :
    G.mixedStoppedPayoffLawFrom
        (h.behavioralToMixedProfile profile)
        current fuel =
      G.behavioralStoppedPayoffLawFrom
        profile current fuel := by
  let hweak :=
    h.toFiniteNoAbsentMindednessHypotheses
  simpa [hweak,
    ObservedGame.FiniteNoAbsentMindednessHypotheses.behavioralToMixedProfile,
    ObservedGame.FiniteNoAbsentMindednessHypotheses.behavioralToMixedStrategy,
    ObservedGame.FiniteKuhnHypotheses.behavioralToMixedProfile,
    ObservedGame.FiniteKuhnHypotheses.behavioralToMixedStrategy,
    ObservedGame.FiniteKuhnHypotheses.toFiniteNoAbsentMindednessHypotheses] using
      G.behavioralToMixed_stoppedPayoffLawFrom_of_noAbsentMindedness
        hweak profile current fuel

/-- Finite, non-absent-minded behavioral strategies map to mixed contingent
plans by one exact continuation-family morphism.  Perfect recall is not
required for this direction. -/
noncomputable def behavioralToMixedContinuationHom_of_noAbsentMindedness
    (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)
    [Fintype N] [DecidableEq N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteNoAbsentMindednessHypotheses)
    (roots : G.observed.RootPresentation)
    (fuel : ℕ) :
    (G.behavioralContinuationFamilyOnRoots roots fuel).Hom
      (G.mixedContinuationFamilyOnRoots roots fuel) where
  rootMap := id
  strategyMap :=
    h.behavioralToMixedStrategy
  outcomeMap := id
  map_declaredRoot := by
    intro current hroot
    exact hroot
  map_outcome := by
    intro current profile
    change
      G.behavioralStoppedPayoffLawFrom
          profile current fuel =
        G.mixedStoppedPayoffLawFrom
          (h.behavioralToMixedProfile profile)
          current fuel
    exact
      (G.behavioralToMixed_stoppedPayoffLawFrom_of_noAbsentMindedness
        h profile current fuel).symm

/-- The weak-hypothesis behavioral-to-mixed morphism covers every admissible
root because its root map is the identity. -/
theorem behavioralToMixedContinuationHom_of_noAbsentMindedness_declaredRootSurjective
    (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)
    [Fintype N] [DecidableEq N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteNoAbsentMindednessHypotheses)
    (roots : G.observed.RootPresentation)
    (fuel : ℕ) :
    (G.behavioralToMixedContinuationHom_of_noAbsentMindedness
      h roots fuel).DeclaredRootSurjective := by
  intro targetRoot htargetRoot
  exact ⟨targetRoot, htargetRoot, rfl⟩

/-- Identity outcome transport preserves every common law utility under the
weak behavioral-sampling hypotheses. -/
theorem behavioralToMixedContinuationHom_of_noAbsentMindedness_utilityCompatible
    (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)
    [Fintype N] [DecidableEq N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteNoAbsentMindednessHypotheses)
    (roots : G.observed.RootPresentation)
    (fuel : ℕ)
    {V : Type*}
    (utility : PMF (Option (N → U)) → N → V) :
    (G.behavioralToMixedContinuationHom_of_noAbsentMindedness
      h roots fuel).UtilityCompatible
        (fun _ => utility)
        (fun _ => utility) := by
  intro current outcome i
  rfl

/-- Mixed bounded Nash on presentation-designated continuations of the independently pre-sampled plan reflects to
behavioral bounded Nash on presentation-designated continuations under finite information and no absent-mindedness.
Perfect recall is not required for this one-way result. -/
theorem isBehavioralNashOnRootsAtFuel_of_behavioralToMixed_of_noAbsentMindedness
    (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)
    [Fintype N] [DecidableEq N]
    [Preorder V]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteNoAbsentMindednessHypotheses)
    (roots : G.observed.RootPresentation)
    (utility :
      PMF (Option (N → U)) → N → V)
    (profile : G.observed.BehavioralProfile)
    (fuel : ℕ)
    (hmixed :
      G.IsMixedNashOnRootsAtFuel
        roots utility
        (h.behavioralToMixedProfile profile)
        fuel) :
    G.IsBehavioralNashOnRootsAtFuel
      roots utility profile fuel := by
  change
    (G.behavioralContinuationFamilyOnRoots
      roots fuel).IsNashOnRoots
        (fun _ => utility) profile
  have hmixed' :
      (G.mixedContinuationFamilyOnRoots
        roots fuel).IsNashOnRoots
          (fun _ => utility)
          (h.behavioralToMixedProfile profile) :=
    hmixed
  exact
    hmixed'.comap
      (G.behavioralToMixedContinuationHom_of_noAbsentMindedness
        h roots fuel)
      (G.behavioralToMixedContinuationHom_of_noAbsentMindedness_utilityCompatible
        h roots fuel utility)

/-- Compatibility wrapper for the behavioral-to-mixed continuation morphism
under the traditional finite perfect-recall hypotheses. -/
noncomputable def behavioralToMixedContinuationHom
    (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)
    [Fintype N] [DecidableEq N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (roots : G.observed.RootPresentation)
    (fuel : ℕ) :
    (G.behavioralContinuationFamilyOnRoots roots fuel).Hom
      (G.mixedContinuationFamilyOnRoots roots fuel) :=
  G.behavioralToMixedContinuationHom_of_noAbsentMindedness
    h.toFiniteNoAbsentMindednessHypotheses roots fuel

/-- The behavioral-to-mixed continuation morphism covers every admissible
root because its root map is the identity. -/
theorem behavioralToMixedContinuationHom_declaredRootSurjective
    (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)
    [Fintype N] [DecidableEq N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (roots : G.observed.RootPresentation)
    (fuel : ℕ) :
    (G.behavioralToMixedContinuationHom
      h roots fuel).DeclaredRootSurjective := by
  intro targetRoot htargetRoot
  exact ⟨targetRoot, htargetRoot, rfl⟩

/-- Identity outcome transport preserves every common law utility. -/
theorem behavioralToMixedContinuationHom_utilityCompatible
    (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)
    [Fintype N] [DecidableEq N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (roots : G.observed.RootPresentation)
    (fuel : ℕ)
    {V : Type*}
    (utility : PMF (Option (N → U)) → N → V) :
    (G.behavioralToMixedContinuationHom
      h roots fuel).UtilityCompatible
        (fun _ => utility)
        (fun _ => utility) := by
  intro current outcome i
  rfl

/-- If the independently sampled mixed profile is bounded Nash on presentation-designated continuations, then the
source behavioral profile is bounded Nash on presentation-designated continuations.

This reflection direction needs only exact realization.  The converse still
requires semantic coverage of arbitrary mixed deviations. -/
theorem isBehavioralNashOnRootsAtFuel_of_behavioralToMixed
    (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)
    [Fintype N] [DecidableEq N]
    [Preorder V]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (roots : G.observed.RootPresentation)
    (utility :
      PMF (Option (N → U)) → N → V)
    (profile : G.observed.BehavioralProfile)
    (fuel : ℕ)
    (hmixed :
      G.IsMixedNashOnRootsAtFuel
        roots utility
        (h.behavioralToMixedProfile profile)
        fuel) :
    G.IsBehavioralNashOnRootsAtFuel
      roots utility profile fuel := by
  change
    (G.behavioralContinuationFamilyOnRoots
      roots fuel).IsNashOnRoots
        (fun _ => utility) profile
  have hmixed' :
      (G.mixedContinuationFamilyOnRoots
        roots fuel).IsNashOnRoots
          (fun _ => utility)
          (h.behavioralToMixedProfile profile) :=
    hmixed
  exact
    hmixed'.comap
      (G.behavioralToMixedContinuationHom
        h roots fuel)
      (G.behavioralToMixedContinuationHom_utilityCompatible
        h roots fuel utility)

/-- Two-way bounded Nash on presentation-designated continuations transfer follows once arbitrary mixed deviations are
semantically realized by behavioral deviations at the source profile.

The premise is deliberately semantic and rootwise; no false literal
surjectivity claim about the two strategy spaces is required. -/
theorem isBehavioralNashOnRootsAtFuel_iff_mixed_of_deviationComplete
    (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)
    [Fintype N] [DecidableEq N]
    [Preorder V]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (roots : G.observed.RootPresentation)
    (utility :
      PMF (Option (N → U)) → N → V)
    (profile : G.observed.BehavioralProfile)
    (fuel : ℕ)
    (hdeviation :
      (G.behavioralToMixedContinuationHom
        h roots fuel).OutcomeDeviationCompleteAt
          profile) :
    G.IsBehavioralNashOnRootsAtFuel
        roots utility profile fuel ↔
      G.IsMixedNashOnRootsAtFuel
        roots utility
        (h.behavioralToMixedProfile profile)
        fuel := by
  exact
    (G.behavioralToMixedContinuationHom
      h roots fuel).isNashOnRoots_iff_of_outcomeDeviationCompleteAt
        (G.behavioralToMixedContinuationHom_utilityCompatible
          h roots fuel utility)
        (G.behavioralToMixedContinuationHom_declaredRootSurjective
          h roots fuel)
        profile
        hdeviation

end ExtensiveGame.ObservedChanceGame
