/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Core
import EconCSLib.GameTheory.ExtensiveGame.Observed.DeferredSampling.Execution

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Execution

Sequential posterior execution and root-scoped payoff-law equality.
-/

namespace ExtensiveGame.ObservedChanceGame

variable {N U : Type*} (G : ObservedChanceGame N U)

/-- At a player history, the stochastic policy induced by a pure profile's
Dirac behavioral embedding is the point mass at that profile's prescribed
concrete action. -/
theorem pureProfile_toBehavioral_toHistoryPolicy_of_mover
    (profile : G.observed.PureProfile)
    (history :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (hnonterminal :
      ¬ G.observed.base.isTerminal history.1)
    (i : N)
    (hmover :
      G.observed.base.mover history.1 = some i) :
    BehavioralProfile.toHistoryPolicy
        G
        (profile.toBehavioral G.observed)
        history hnonterminal =
      PMF.pure
        (profile.actionAt
          G.observed history i hmover) := by
  rw [BehavioralProfile.toHistoryPolicy_of_mover
    G (profile.toBehavioral G.observed)
    history hnonterminal i hmover]
  unfold ObservedGame.BehavioralProfile.actionLawAt
    ObservedGame.BehavioralStrategy.actionLawAt
    ObservedGame.PureProfile.toBehavioral
    ObservedGame.PureStrategy.toBehavioral
    ObservedGame.PureProfile.actionAt
    ObservedGame.PureStrategy.actionAt
  rw [PMF.pure_map]

/-- Sequential posterior exposure of arbitrary mixed pure plans has exactly
the same bounded complete-history law as the root-scoped conditional
behavioral profile.

The theorem is strengthened over all suffixes of the selected root.  Its
source law samples each player's current posterior plan independently; its
target keeps the single behavioral strategy fixed from the original root.
This is the induction invariant needed for exact mixed-to-behavioral
realization. -/
theorem posteriorMixedHistoryLawAlong_eq_behavioral
    [Fintype N] [DecidableEq N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (certificate : G.observed.RecallCertificate)
    (profile : G.observed.MixedProfile)
    (root :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    {finish : G.observed.base.State}
    (suffix :
      G.observed.base.toArena.History
        root.1 finish)
    (fuel : ℕ) :
    let current :
        G.observed.base.toArena.HistoryFrom
          G.observed.base.init :=
      ⟨finish, root.2.append suffix⟩
    ((profile.posteriorAfterDecisions
        G.observed
        (G.observed.relativeOwnDecisionHistories
          root current)).pureProfileLaw
          G.observed).bind
      (fun pureProfile =>
        G.observed.base.toArena.stochasticHistoryPMFFrom
          (BehavioralProfile.toHistoryPolicy G
            (pureProfile.toBehavioral G.observed))
          current fuel) =
      G.observed.base.toArena.stochasticHistoryPMFFrom
        (BehavioralProfile.toHistoryPolicy G
          (certificate.behavioralizeMixedProfileFrom
            G.observed root profile))
        current fuel := by
  induction fuel generalizing finish with
  | zero =>
      simp
  | succ fuel ih =>
      let current :
          G.observed.base.toArena.HistoryFrom
            G.observed.base.init :=
        ⟨finish, root.2.append suffix⟩
      let posteriorProfile :
          G.observed.MixedProfile :=
        profile.posteriorAfterDecisions
          G.observed
          (G.observed.relativeOwnDecisionHistories
            root current)
      let behavioralProfile :
          G.observed.BehavioralProfile :=
        certificate.behavioralizeMixedProfileFrom
          G.observed root profile
      change
        (posteriorProfile.pureProfileLaw
          G.observed).bind
            (fun pureProfile =>
              G.observed.base.toArena.stochasticHistoryPMFFrom
                (BehavioralProfile.toHistoryPolicy G
                  (pureProfile.toBehavioral
                    G.observed))
                current (fuel + 1)) =
          G.observed.base.toArena.stochasticHistoryPMFFrom
            (BehavioralProfile.toHistoryPolicy G
              behavioralProfile)
            current (fuel + 1)
      by_cases hterminal :
          G.observed.base.isTerminal current.1
      · simp [Arena.stochasticHistoryPMFFrom,
          hterminal]
      · rw [G.observed.base.toArena.stochasticHistoryPMFFrom_succ_of_not_terminal
          (BehavioralProfile.toHistoryPolicy G
            behavioralProfile)
          current fuel hterminal]
        simp_rw [Arena.stochasticHistoryPMFFrom,
          dif_neg hterminal]
        cases hmover :
            G.observed.base.mover current.1 with
        | none =>
            have hchanceSource
                (pureProfile :
                  G.observed.PureProfile) :
                BehavioralProfile.toHistoryPolicy
                    G
                    (pureProfile.toBehavioral
                      G.observed)
                    current hterminal =
                  G.chanceKernel current
                    ⟨hmover, hterminal⟩ :=
              BehavioralProfile.toHistoryPolicy_of_chance
                G
                (pureProfile.toBehavioral
                  G.observed)
                current hterminal hmover
            have hchanceTarget :
                BehavioralProfile.toHistoryPolicy
                    G behavioralProfile
                    current hterminal =
                  G.chanceKernel current
                    ⟨hmover, hterminal⟩ :=
              BehavioralProfile.toHistoryPolicy_of_chance
                G behavioralProfile
                current hterminal hmover
            simp_rw [hchanceSource]
            rw [hchanceTarget]
            rw [PMF.bind_comm]
            apply congrArg
              (fun continuation =>
                (G.chanceKernel current
                  ⟨hmover, hterminal⟩).bind
                    continuation)
            funext action
            have hrelative :
                G.observed.relativeOwnDecisionHistories
                    root
                    ⟨G.observed.base.next
                        finish action,
                      (root.2.append suffix).snoc
                        action⟩ =
                  G.observed.relativeOwnDecisionHistories
                    root current := by
              funext i
              apply
                (G.observed.relativeOwnDecisionHistories_snoc_of_not_mover
                  root suffix action i)
              simp [current, hmover]
            have ihAction :=
              ih
                (suffix := suffix.snoc action)
            dsimp only at ihAction
            rw [Arena.History.append_snoc,
              hrelative] at ihAction
            change
              (posteriorProfile.pureProfileLaw
                G.observed).bind
                  (fun pureProfile =>
                    G.observed.base.toArena.stochasticHistoryPMFFrom
                      (BehavioralProfile.toHistoryPolicy G
                        (pureProfile.toBehavioral
                          G.observed))
                      ⟨G.observed.base.next
                          finish action,
                        root.2.append
                          (suffix.snoc action)⟩
                      fuel) =
                G.observed.base.toArena.stochasticHistoryPMFFrom
                  (BehavioralProfile.toHistoryPolicy G
                    behavioralProfile)
                  ⟨G.observed.base.next
                      finish action,
                    root.2.append
                      (suffix.snoc action)⟩
                  fuel
            simpa [posteriorProfile,
              behavioralProfile, current,
              Arena.History.append_snoc] using
                ihAction
        | some i =>
            have hmover' :
                G.observed.base.mover finish =
                  some i := by
              simpa [current] using hmover
            let information :=
              G.observed.infoAt
                current i hmover
            let abstractToConcrete :=
              G.observed.actionEquiv
                current i hmover
            let currentPlanLaw :
                PMF
                  (G.observed.PureStrategy i) :=
              posteriorProfile i
            have hpureStep
                (pureProfile :
                  G.observed.PureProfile) :
                BehavioralProfile.toHistoryPolicy
                    G
                    (pureProfile.toBehavioral
                      G.observed)
                    current hterminal =
                  PMF.pure
                    (abstractToConcrete
                      (pureProfile i
                        information)) := by
              simpa [abstractToConcrete,
                information] using
                G.pureProfile_toBehavioral_toHistoryPolicy_of_mover
                  pureProfile current hterminal
                  i hmover
            simp_rw [hpureStep, PMF.pure_bind]
            have htargetAction :
                BehavioralProfile.toHistoryPolicy
                    G behavioralProfile
                    current hterminal =
                  (currentPlanLaw.map
                    (fun pureStrategy =>
                      pureStrategy information)).map
                        abstractToConcrete := by
              rw [BehavioralProfile.toHistoryPolicy_of_mover
                G behavioralProfile current
                hterminal i hmover]
              unfold
                ObservedGame.BehavioralProfile.actionLawAt
                ObservedGame.BehavioralStrategy.actionLawAt
              change
                (certificate.behavioralizeMixedFrom
                    G.observed root i (profile i)
                    information).map
                      abstractToConcrete =
                  _
              rw [certificate.behavioralizeMixedFrom_at_append
                G.observed root suffix i hmover'
                (profile i)]
              rfl
            rw [htargetAction, PMF.bind_map]
            let continuation :
                G.observed.InfoAction i information →
                  G.observed.PureProfile →
                    PMF
                      (G.observed.base.toArena.HistoryFrom
                        G.observed.base.init) :=
              fun abstractAction pureProfile =>
                G.observed.base.toArena.stochasticHistoryPMFFrom
                  (BehavioralProfile.toHistoryPolicy G
                    (pureProfile.toBehavioral
                      G.observed))
                  ⟨G.observed.base.next
                      finish
                      (abstractToConcrete
                        abstractAction),
                    root.2.append
                      (suffix.snoc
                        (abstractToConcrete
                          abstractAction))⟩
                  fuel
            have hdisintegrate :=
              PMF.fintypePi_bind_conditionOnCoordinate
                posteriorProfile i
                (fun pureStrategy =>
                  pureStrategy information)
                continuation
            change
              (posteriorProfile.pureProfileLaw
                G.observed).bind
                  (fun pureProfile =>
                    continuation
                      (pureProfile i information)
                      pureProfile) =
                (currentPlanLaw.map
                  (fun pureStrategy =>
                    pureStrategy information)).bind
                  (fun abstractAction =>
                    G.observed.base.toArena.stochasticHistoryPMFFrom
                      (BehavioralProfile.toHistoryPolicy G
                        behavioralProfile)
                      ⟨G.observed.base.next
                          finish
                          (abstractToConcrete
                            abstractAction),
                        root.2.append
                          (suffix.snoc
                            (abstractToConcrete
                              abstractAction))⟩
                      fuel)
            unfold
              ObservedGame.MixedProfile.pureProfileLaw
            refine hdisintegrate.symm.trans ?_
            apply congrArg
              (fun next =>
                (currentPlanLaw.map
                  (fun pureStrategy =>
                    pureStrategy information)).bind
                    next)
            funext abstractAction
            have hposteriorUpdate :=
              profile.posteriorAfterDecisions_relative_snoc_of_mover
                G.observed root suffix i hmover'
                abstractAction
            have ihAction :=
              ih
                (suffix :=
                  suffix.snoc
                    (abstractToConcrete
                      abstractAction))
            dsimp only at ihAction
            rw [Arena.History.append_snoc] at hposteriorUpdate ihAction
            rw [hposteriorUpdate] at ihAction
            unfold
              ObservedGame.MixedProfile.pureProfileLaw
                at ihAction
            change
              (PMF.fintypePi
                (Function.update posteriorProfile i
                  (currentPlanLaw.conditionOnFiber
                    (fun pureStrategy =>
                      pureStrategy information)
                    abstractAction))).bind
                  (continuation abstractAction) =
                G.observed.base.toArena.stochasticHistoryPMFFrom
                  (BehavioralProfile.toHistoryPolicy G
                    behavioralProfile)
                  ⟨G.observed.base.next
                      finish
                      (abstractToConcrete
                        abstractAction),
                    root.2.append
                      (suffix.snoc
                        (abstractToConcrete
                          abstractAction))⟩
                  fuel
            simpa [posteriorProfile,
              currentPlanLaw, information,
              abstractToConcrete,
              behavioralProfile, current,
              continuation] using ihAction

/-- From the selected root itself, an arbitrary mixed profile and its
root-scoped conditional behavioralization have identical bounded complete
history laws. -/
theorem mixedToBehavioral_stoppedHistoryLawFrom
    [Fintype N] [DecidableEq N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (certificate : G.observed.RecallCertificate)
    (profile : G.observed.MixedProfile)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) :
    G.mixedStoppedHistoryLawFrom
        profile current fuel =
      G.observed.base.toArena.stochasticHistoryPMFFrom
        (BehavioralProfile.toHistoryPolicy G
          (certificate.behavioralizeMixedProfileFrom
            G.observed current profile))
        current fuel := by
  have hrealization :=
    G.posteriorMixedHistoryLawAlong_eq_behavioral
      certificate profile current
      (Arena.History.nil :
        G.observed.base.toArena.History
          current.1 current.1)
      fuel
  have hrelative :
      G.observed.relativeOwnDecisionHistories
          current current =
        fun _ => [] := by
    funext i
    exact
      G.observed.relativeOwnDecisionHistories_self
        current i
  dsimp only at hrealization
  rw [Arena.History.append_nil] at hrealization
  rw [hrelative,
    ObservedGame.MixedProfile.posteriorAfterDecisions_empty]
      at hrealization
  simpa [mixedStoppedHistoryLawFrom]
    using hrealization

/-- Root-scoped conditional behavioralization preserves the complete bounded
optional-payoff law of every arbitrary mixed profile. -/
theorem mixedToBehavioral_stoppedPayoffLawFrom
    [Fintype N] [DecidableEq N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (certificate : G.observed.RecallCertificate)
    (profile : G.observed.MixedProfile)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) :
    G.mixedStoppedPayoffLawFrom
        profile current fuel =
      G.behavioralStoppedPayoffLawFrom
        (certificate.behavioralizeMixedProfileFrom
          G.observed current profile)
        current fuel := by
  calc
    G.mixedStoppedPayoffLawFrom
        profile current fuel =
      (G.mixedStoppedHistoryLawFrom
        profile current fuel).map
          G.stoppedPayoffAtHistory :=
      G.mixedStoppedPayoffLawFrom_eq_map_history
        profile current fuel
    _ =
      (G.observed.base.toArena.stochasticHistoryPMFFrom
        (BehavioralProfile.toHistoryPolicy G
          (certificate.behavioralizeMixedProfileFrom
            G.observed current profile))
        current fuel).map
          G.stoppedPayoffAtHistory := by
      rw [G.mixedToBehavioral_stoppedHistoryLawFrom
        certificate profile current fuel]
    _ =
      G.behavioralStoppedPayoffLawFrom
        (certificate.behavioralizeMixedProfileFrom
          G.observed current profile)
        current fuel :=
      rfl


end ExtensiveGame.ObservedChanceGame
