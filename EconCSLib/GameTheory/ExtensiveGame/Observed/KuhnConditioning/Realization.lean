/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Execution
import EconCSLib.GameTheory.ExtensiveGame.Observed.DeferredSampling.Realization

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Realization

Root-scoped law morphisms, deviation coverage, and finite Kuhn transfer.

The mathematical realization target is [Kuhn 1953, §4, Thm. 4] under finite
perfect recall. This module's exact bounded history/payoff-law equalities and
Nash-transfer morphisms are the occurrence-sensitive `PMF` implementation of
that target. They do not assert equality of arbitrary infinite path measures.
-/

namespace ExtensiveGame.ObservedChanceGame

universe uN uU uAS uO uI uP

variable {N : Type uN} {U : Type uU}
  (G : ObservedChanceGame.{uN, uU, uAS, uAS, uO, uI, uP} N U)

/-- Exact root-scoped conditional behavioralization as a law-game morphism.

This morphism already gives exact outcome-law realization.  Two-way Nash
transfer additionally needs semantic coverage of arbitrary behavioral
deviations, proved separately from the law equality. -/
noncomputable def mixedToBehavioralLawHomAt
    [Fintype N] [DecidableEq N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (certificate : G.observed.RecallCertificate)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) :
    (G.mixedLawGameForm current fuel).Hom
      (G.behavioralLawGameForm current fuel) where
  strategyMap :=
    fun i strategy =>
      certificate.behavioralizeMixedFrom
        G.observed current i strategy
  outcomeMap := id
  map_outcomeLaw := by
    intro profile
    unfold LawGameForm.RealizesVia
    change
      (G.mixedStoppedPayoffLawFrom
        profile current fuel).map id =
      G.behavioralStoppedPayoffLawFrom
        (certificate.behavioralizeMixedProfileFrom
          G.observed current profile)
        current fuel
    rw [PMF.map_id]
    exact
      G.mixedToBehavioral_stoppedPayoffLawFrom
        certificate profile current fuel

/-- Replacing one root-scoped behavioralized component by an arbitrary
behavioral strategy has the same bounded history law as replacing the source
mixed component by that strategy's independently sampled complete table.

The statement is strengthened along every suffix of the selected root so that
the proof can recurse through stochastic execution. -/
theorem behavioralDeviationHistoryLawAlong_eq
    [Fintype N] [DecidableEq N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (profile : G.observed.MixedProfile)
    (root :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (who : N)
    (target :
      G.observed.BehavioralStrategy who)
    {finish : G.observed.base.State}
    (suffix :
      G.observed.base.toArena.History
        root.1 finish)
    (fuel : ℕ) :
    let sourceDeviation :
        G.observed.MixedProfile :=
      Function.update profile who
        (h.behavioralToMixedStrategy
          who target)
    let baseBehavior :
        G.observed.BehavioralProfile :=
      h.recallCertificate.behavioralizeMixedProfileFrom
        G.observed root profile
    let targetBehavior :
        G.observed.BehavioralProfile :=
      Function.update baseBehavior who target
    let realizedBehavior :
        G.observed.BehavioralProfile :=
      h.recallCertificate.behavioralizeMixedProfileFrom
        G.observed root sourceDeviation
    let current :
        G.observed.base.toArena.HistoryFrom
          G.observed.base.init :=
      ⟨finish, root.2.append suffix⟩
    G.observed.base.toArena.stochasticHistoryPMFFrom
        (BehavioralProfile.toHistoryPolicy G
          targetBehavior)
        current fuel =
      G.observed.base.toArena.stochasticHistoryPMFFrom
        (BehavioralProfile.toHistoryPolicy G
          realizedBehavior)
        current fuel := by
  induction fuel generalizing finish with
  | zero =>
      rfl
  | succ fuel ih =>
      let sourceDeviation :
          G.observed.MixedProfile :=
        Function.update profile who
          (h.behavioralToMixedStrategy
            who target)
      let baseBehavior :
          G.observed.BehavioralProfile :=
        h.recallCertificate.behavioralizeMixedProfileFrom
          G.observed root profile
      let targetBehavior :
          G.observed.BehavioralProfile :=
        Function.update baseBehavior who target
      let realizedBehavior :
          G.observed.BehavioralProfile :=
        h.recallCertificate.behavioralizeMixedProfileFrom
          G.observed root sourceDeviation
      let current :
          G.observed.base.toArena.HistoryFrom
            G.observed.base.init :=
        ⟨finish, root.2.append suffix⟩
      change
        G.observed.base.toArena.stochasticHistoryPMFFrom
            (BehavioralProfile.toHistoryPolicy G
              targetBehavior)
            current (fuel + 1) =
          G.observed.base.toArena.stochasticHistoryPMFFrom
            (BehavioralProfile.toHistoryPolicy G
              realizedBehavior)
            current (fuel + 1)
      by_cases hterminal :
          G.observed.base.isTerminal current.1
      · simp [Arena.stochasticHistoryPMFFrom,
          hterminal]
      · rw [G.observed.base.toArena.stochasticHistoryPMFFrom_succ_of_not_terminal
          (BehavioralProfile.toHistoryPolicy G
            targetBehavior)
          current fuel hterminal]
        rw [G.observed.base.toArena.stochasticHistoryPMFFrom_succ_of_not_terminal
          (BehavioralProfile.toHistoryPolicy G
            realizedBehavior)
          current fuel hterminal]
        have hpolicy :
            BehavioralProfile.toHistoryPolicy G
                targetBehavior current hterminal =
              BehavioralProfile.toHistoryPolicy G
                realizedBehavior current hterminal := by
          cases hmover :
              G.observed.base.mover current.1 with
          | none =>
              rw [BehavioralProfile.toHistoryPolicy_of_chance
                G targetBehavior current
                hterminal hmover]
              rw [BehavioralProfile.toHistoryPolicy_of_chance
                G realizedBehavior current
                hterminal hmover]
          | some mover =>
              rw [BehavioralProfile.toHistoryPolicy_of_mover
                G targetBehavior current
                hterminal mover hmover]
              rw [BehavioralProfile.toHistoryPolicy_of_mover
                G realizedBehavior current
                hterminal mover hmover]
              unfold
                ObservedGame.BehavioralProfile.actionLawAt
                ObservedGame.BehavioralStrategy.actionLawAt
              apply congrArg
                (fun abstractLaw :
                    PMF
                      (G.observed.InfoAction mover
                        (G.observed.infoAt
                          current mover hmover hterminal)) =>
                  abstractLaw.map
                    (G.observed.actionEquiv
                      current mover hmover hterminal))
              by_cases hmoverWho :
                  mover = who
              · subst mover
                have hmover' :
                    G.observed.base.mover finish =
                      some who := by
                  simpa [current] using hmover
                have hnonterminal' :
                    ¬ G.observed.base.isTerminal finish := by
                  simpa [current] using hterminal
                simp only [targetBehavior,
                  realizedBehavior, sourceDeviation,
                  ObservedGame.RecallCertificate.behavioralizeMixedProfileFrom,
                  Function.update]
                change
                  target
                      (G.observed.infoAt
                        current who hmover hterminal) =
                    h.recallCertificate.behavioralizeMixedFrom
                      G.observed root who
                      (h.behavioralToMixedStrategy
                        who target)
                      (G.observed.infoAt
                        current who hmover hterminal)
                exact
                  (h.behavioralize_behavioralToMixed_at_append
                    G.observed root suffix who hmover' hnonterminal'
                    target).symm
              · simp [targetBehavior,
                  realizedBehavior, baseBehavior,
                  sourceDeviation,
                  ObservedGame.RecallCertificate.behavioralizeMixedProfileFrom,
                  Function.update, hmoverWho]
        rw [hpolicy]
        apply congrArg
          (fun continuation =>
            (BehavioralProfile.toHistoryPolicy G
              realizedBehavior current
              hterminal).bind continuation)
        funext action
        have ihAction :=
          ih
            (suffix := suffix.snoc action)
        simpa [sourceDeviation,
          baseBehavior, targetBehavior,
          realizedBehavior, current,
          Arena.History.append_snoc] using
            ihAction

/-- Root-scoped behavioralization of an independently sampled behavioral
profile is behaviorally indistinguishable from the original profile, even
after an arbitrary unilateral behavioral deviation.

Only the non-deviating players use the table behavioralization; their local
laws agree with the source behavioral strategies at every history reachable
from the selected root. -/
theorem behavioralTableDeviationHistoryLawAlong_eq
    [Fintype N] [DecidableEq N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (profile : G.observed.BehavioralProfile)
    (root :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (who : N)
    (target :
      G.observed.BehavioralStrategy who)
    {finish : G.observed.base.State}
    (suffix :
      G.observed.base.toArena.History
        root.1 finish)
    (fuel : ℕ) :
    let mixedProfile :=
      h.behavioralToMixedProfile profile
    let mappedProfile :=
      h.mixedToBehavioralProfileAt
        G.observed root mixedProfile
    let sourceDeviation :=
      Function.update profile who target
    let mappedDeviation :=
      Function.update mappedProfile who target
    let current :
        G.observed.base.toArena.HistoryFrom
          G.observed.base.init :=
      ⟨finish, root.2.append suffix⟩
    G.observed.base.toArena.stochasticHistoryPMFFrom
        (BehavioralProfile.toHistoryPolicy G
          sourceDeviation)
        current fuel =
      G.observed.base.toArena.stochasticHistoryPMFFrom
        (BehavioralProfile.toHistoryPolicy G
          mappedDeviation)
        current fuel := by
  induction fuel generalizing finish with
  | zero =>
      rfl
  | succ fuel ih =>
      let mixedProfile :=
        h.behavioralToMixedProfile profile
      let mappedProfile :=
        h.mixedToBehavioralProfileAt
          G.observed root mixedProfile
      let sourceDeviation :=
        Function.update profile who target
      let mappedDeviation :=
        Function.update mappedProfile who target
      let current :
          G.observed.base.toArena.HistoryFrom
            G.observed.base.init :=
        ⟨finish, root.2.append suffix⟩
      change
        G.observed.base.toArena.stochasticHistoryPMFFrom
            (BehavioralProfile.toHistoryPolicy G
              sourceDeviation)
            current (fuel + 1) =
          G.observed.base.toArena.stochasticHistoryPMFFrom
            (BehavioralProfile.toHistoryPolicy G
              mappedDeviation)
            current (fuel + 1)
      by_cases hterminal :
          G.observed.base.isTerminal current.1
      · simp [Arena.stochasticHistoryPMFFrom,
          hterminal]
      · rw [G.observed.base.toArena.stochasticHistoryPMFFrom_succ_of_not_terminal
          (BehavioralProfile.toHistoryPolicy G
            sourceDeviation)
          current fuel hterminal]
        rw [G.observed.base.toArena.stochasticHistoryPMFFrom_succ_of_not_terminal
          (BehavioralProfile.toHistoryPolicy G
            mappedDeviation)
          current fuel hterminal]
        have hpolicy :
            BehavioralProfile.toHistoryPolicy G
                sourceDeviation current hterminal =
              BehavioralProfile.toHistoryPolicy G
                mappedDeviation current hterminal := by
          cases hmover :
              G.observed.base.mover current.1 with
          | none =>
              rw [BehavioralProfile.toHistoryPolicy_of_chance
                G sourceDeviation current
                hterminal hmover]
              rw [BehavioralProfile.toHistoryPolicy_of_chance
                G mappedDeviation current
                hterminal hmover]
          | some mover =>
              rw [BehavioralProfile.toHistoryPolicy_of_mover
                G sourceDeviation current
                hterminal mover hmover]
              rw [BehavioralProfile.toHistoryPolicy_of_mover
                G mappedDeviation current
                hterminal mover hmover]
              unfold
                ObservedGame.BehavioralProfile.actionLawAt
                ObservedGame.BehavioralStrategy.actionLawAt
              apply congrArg
                (fun abstractLaw :
                    PMF
                      (G.observed.InfoAction mover
                        (G.observed.infoAt
                          current mover hmover hterminal)) =>
                  abstractLaw.map
                    (G.observed.actionEquiv
                      current mover hmover hterminal))
              by_cases hmoverWho :
                  mover = who
              · subst mover
                simp [sourceDeviation,
                  mappedDeviation]
              · have hmover' :
                    G.observed.base.mover finish =
                      some mover := by
                  simpa [current] using hmover
                have hnonterminal' :
                    ¬ G.observed.base.isTerminal finish := by
                  simpa [current] using hterminal
                simp only [sourceDeviation,
                  mappedDeviation, mappedProfile,
                  mixedProfile,
                  ObservedGame.FiniteKuhnHypotheses.mixedToBehavioralProfileAt,
                  ObservedGame.FiniteKuhnHypotheses.behavioralToMixedProfile,
                  ObservedGame.RecallCertificate.behavioralizeMixedProfileFrom,
                  Function.update, hmoverWho]
                change
                  profile mover
                      (G.observed.infoAt
                        current mover hmover hterminal) =
                    h.recallCertificate.behavioralizeMixedFrom
                      G.observed root mover
                      (h.behavioralToMixedStrategy
                        mover (profile mover))
                      (G.observed.infoAt
                        current mover hmover hterminal)
                exact
                  (h.behavioralize_behavioralToMixed_at_append
                    G.observed root suffix mover
                    hmover' hnonterminal'
                    (profile mover)).symm
        rw [hpolicy]
        apply congrArg
          (fun continuation =>
            (BehavioralProfile.toHistoryPolicy G
              mappedDeviation current
              hterminal).bind continuation)
        funext action
        have ihAction :=
          ih
            (suffix := suffix.snoc action)
        simpa [mixedProfile, mappedProfile,
          sourceDeviation, mappedDeviation,
          current, Arena.History.append_snoc]
            using ihAction

/-- Payoff-law form of table behavioralization equivalence under an arbitrary
unilateral behavioral deviation. -/
theorem behavioralTableDeviationPayoffLaw_eq
    [Fintype N] [DecidableEq N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (profile : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (who : N)
    (target :
      G.observed.BehavioralStrategy who)
    (fuel : ℕ) :
    G.behavioralStoppedPayoffLawFrom
        (Function.update profile who target)
        current fuel =
      G.behavioralStoppedPayoffLawFrom
        (Function.update
          (h.mixedToBehavioralProfileAt
            G.observed current
            (h.behavioralToMixedProfile
              profile))
          who target)
        current fuel := by
  have hhistory :=
    G.behavioralTableDeviationHistoryLawAlong_eq
      h profile current who target
      (Arena.History.nil :
        G.observed.base.toArena.History
          current.1 current.1)
      fuel
  dsimp only at hhistory
  rw [Arena.History.append_nil] at hhistory
  exact
    congrArg
      (fun law =>
        law.map G.stoppedPayoffAtHistory)
      hhistory

/-- Exact payoff-law realization of an arbitrary unilateral behavioral
deviation by independently sampling that deviating behavioral strategy's
complete contingent table. -/
theorem behavioralDeviationPayoffLaw_eq_mixed
    [Fintype N] [DecidableEq N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (profile : G.observed.MixedProfile)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (who : N)
    (target :
      G.observed.BehavioralStrategy who)
    (fuel : ℕ) :
    G.behavioralStoppedPayoffLawFrom
        (Function.update
          (h.mixedToBehavioralProfileAt
            G.observed current profile)
          who target)
        current fuel =
      G.mixedStoppedPayoffLawFrom
        (Function.update profile who
          (h.behavioralToMixedStrategy
            who target))
        current fuel := by
  let sourceDeviation :
      G.observed.MixedProfile :=
    Function.update profile who
      (h.behavioralToMixedStrategy
        who target)
  let targetBehavior :
      G.observed.BehavioralProfile :=
    Function.update
      (h.mixedToBehavioralProfileAt
        G.observed current profile)
      who target
  let realizedBehavior :
      G.observed.BehavioralProfile :=
    h.mixedToBehavioralProfileAt
      G.observed current sourceDeviation
  have hhistory :=
    G.behavioralDeviationHistoryLawAlong_eq
      h profile current who target
      (Arena.History.nil :
        G.observed.base.toArena.History
          current.1 current.1)
      fuel
  dsimp only at hhistory
  rw [Arena.History.append_nil] at hhistory
  calc
    G.behavioralStoppedPayoffLawFrom
        targetBehavior current fuel =
      (G.observed.base.toArena.stochasticHistoryPMFFrom
        (BehavioralProfile.toHistoryPolicy G
          targetBehavior)
        current fuel).map
          G.stoppedPayoffAtHistory :=
      rfl
    _ =
      (G.observed.base.toArena.stochasticHistoryPMFFrom
        (BehavioralProfile.toHistoryPolicy G
          realizedBehavior)
        current fuel).map
          G.stoppedPayoffAtHistory := by
      exact
        congrArg
          (fun law =>
            law.map G.stoppedPayoffAtHistory)
          hhistory
    _ =
      G.behavioralStoppedPayoffLawFrom
        realizedBehavior current fuel :=
      rfl
    _ =
      G.mixedStoppedPayoffLawFrom
        sourceDeviation current fuel := by
      exact
        (G.mixedToBehavioral_stoppedPayoffLawFrom
          h.recallCertificate sourceDeviation
          current fuel).symm

/-- The finite perfect-recall hypotheses construct the complete root-scoped
mixed-to-behavioral realization certificate, including semantic coverage of
all unilateral behavioral deviations. -/
noncomputable def finiteKuhnMixedBehavioralRealizationAt
    [Fintype N] [DecidableEq N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) :
    G.MixedBehavioralRealizationAt
      current fuel where
  behavioralize :=
    fun i strategy =>
      h.recallCertificate.behavioralizeMixedFrom
        G.observed current i strategy
  map_payoffLaw := by
    intro profile
    exact
      (G.mixedToBehavioral_stoppedPayoffLawFrom
        h.recallCertificate profile
        current fuel).symm
  realize_deviation := by
    intro profile i target
    exact
      ⟨h.behavioralToMixedStrategy i target,
        G.behavioralDeviationPayoffLaw_eq_mixed
          h profile current i target fuel⟩

/-- The behavioral-to-mixed continuation morphism has exact rootwise semantic
coverage of every arbitrary mixed deviation under finite perfect recall.

The realizing behavioral deviation is the root-scoped conditional
behavioralization of the target mixed plan.  Non-deviating independently
sampled behavioral tables are replaced by their original behavioral
strategies using the reachable-history equivalence above. -/
theorem behavioralToMixedContinuationHom_outcomeDeviationCompleteAt
    [Fintype N] [DecidableEq N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (roots : G.observed.RootPresentation)
    (profile : G.observed.BehavioralProfile)
    (fuel : ℕ) :
    (G.behavioralToMixedContinuationHom
      h roots fuel).OutcomeDeviationCompleteAt
        profile := by
  intro current _ i targetMixed
  let sourceBehavior :
      G.observed.BehavioralStrategy i :=
    h.recallCertificate.behavioralizeMixedFrom
      G.observed current i targetMixed
  refine ⟨sourceBehavior, ?_⟩
  dsimp only [
    ContinuationGameForm.Hom.atHom,
    GameForm.Hom.mapProfile,
    ContinuationGameForm.toGameForm,
    behavioralToMixedContinuationHom,
    behavioralContinuationFamilyOnRoots,
    mixedContinuationFamilyOnRoots,
    ObservedGame.FiniteKuhnHypotheses.behavioralToMixedProfile]
  change
    G.mixedStoppedPayoffLawFrom
        (Function.update
          (h.behavioralToMixedProfile profile)
          i targetMixed)
        current fuel =
      (G.behavioralStoppedPayoffLawFrom
        (Function.update profile i sourceBehavior)
        current fuel)
  let mixedDeviation :
      G.observed.MixedProfile :=
    Function.update
      (h.behavioralToMixedProfile profile)
      i targetMixed
  let mappedBase :
      G.observed.BehavioralProfile :=
    h.mixedToBehavioralProfileAt
      G.observed current
      (h.behavioralToMixedProfile profile)
  let mappedDeviation :
      G.observed.BehavioralProfile :=
    h.mixedToBehavioralProfileAt
      G.observed current mixedDeviation
  have hmapped :
      mappedDeviation =
        Function.update mappedBase
          i sourceBehavior := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [mappedDeviation,
        mixedDeviation, sourceBehavior,
        ObservedGame.FiniteKuhnHypotheses.mixedToBehavioralProfileAt,
        Function.update]
    · simp [mappedDeviation, mappedBase,
        mixedDeviation,
        ObservedGame.FiniteKuhnHypotheses.mixedToBehavioralProfileAt,
        Function.update, hji]
  calc
    G.mixedStoppedPayoffLawFrom
        mixedDeviation current fuel =
      G.behavioralStoppedPayoffLawFrom
        mappedDeviation current fuel :=
      G.mixedToBehavioral_stoppedPayoffLawFrom
        h.recallCertificate mixedDeviation
        current fuel
    _ =
      G.behavioralStoppedPayoffLawFrom
        (Function.update mappedBase
          i sourceBehavior)
        current fuel := by
      rw [hmapped]
    _ =
      G.behavioralStoppedPayoffLawFrom
        (Function.update profile
          i sourceBehavior)
        current fuel := by
      exact
        (G.behavioralTableDeviationPayoffLaw_eq
          h profile current i sourceBehavior
          fuel).symm

/-- Full bounded Kuhn designated-continuation theorem: under finite perfect
recall, a behavioral profile is Nash on every presentation-designated
continuation exactly when its independently sampled complete pure-plan
profile has the corresponding mixed-strategy property.

This discharges the semantic-deviation premise of the earlier conditional Nash on presentation-designated continuations
bridge; it does not claim a false root-independent strategy-space
isomorphism. -/
theorem isBehavioralNashOnRootsAtFuel_iff_mixed
    [Fintype N] [DecidableEq N]
    [Preorder V]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (roots : G.observed.RootPresentation)
    (utility :
      PMF (Option (N → U)) → N → V)
    (profile : G.observed.BehavioralProfile)
    (fuel : ℕ) :
    G.IsBehavioralNashOnRootsAtFuel
        roots utility profile fuel ↔
      G.IsMixedNashOnRootsAtFuel
        roots utility
        (h.behavioralToMixedProfile profile)
        fuel := by
  exact
    G.isBehavioralNashOnRootsAtFuel_iff_mixed_of_deviationComplete
      h roots utility profile fuel
      (G.behavioralToMixedContinuationHom_outcomeDeviationCompleteAt
        h roots profile fuel)

/-- Constructive root-scoped Kuhn realization gives two-way Nash transfer for
every utility functional on the complete bounded payoff law. -/
theorem finiteKuhn_isNash_iff
    [Fintype N] [DecidableEq N]
    [Preorder V]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (utility :
      PMF (Option (N → U)) → N → V)
    (profile : G.observed.MixedProfile)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) :
    (G.mixedLawGameForm current fuel).IsNash
        utility profile ↔
      (G.behavioralLawGameForm
        current fuel).IsNash
          utility
      (h.mixedToBehavioralProfileAt
            G.observed current profile) := by
  exact
    (G.finiteKuhnMixedBehavioralRealizationAt
      h current fuel).isNash_iff
      utility profile

/-- The finite Kuhn package specializes the broader countably-supported,
bounded-history realization theorem by supplying its recall certificate.

Finite information is not consumed by the law equality itself; it is needed
later for behavioral-deviation coverage and hence the two-way Nash theorem
above. -/
theorem finiteKuhn_boundedHistoryLaw_specialization
    [Fintype N] [DecidableEq N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (h : G.observed.FiniteKuhnHypotheses)
    (profile : G.observed.MixedProfile)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) :
    G.mixedStoppedHistoryLawFrom profile current fuel =
      G.observed.base.toArena.stochasticHistoryPMFFrom
        (BehavioralProfile.toHistoryPolicy G
          (h.recallCertificate.behavioralizeMixedProfileFrom
            G.observed current profile))
        current fuel :=
  G.countablySupportedMixedToBehavioral_boundedHistoryLaw
    h.recallCertificate profile current fuel

end ExtensiveGame.ObservedChanceGame
