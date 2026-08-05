/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.PMF.DeferredSampling
import EconCSLib.GameTheory.ExtensiveGame.Observed.Kuhn

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.DeferredSampling.Core

Decision keys, freshness invariants, and finite-information table laws.
-/

namespace ExtensiveGame.ObservedGame

universe uN uU

variable {N : Type uN} {U : Type uU}

/-- A global strategic randomization key: one player and one of that
player's decision information states. -/
abbrev DecisionKey (G : ObservedGame N U) :=
  Σ i : N, G.InfoState i

/-- The dependent action value stored at a global decision key. -/
abbrev DecisionValue (G : ObservedGame N U)
    (key : G.DecisionKey) :=
  G.InfoAction key.1 key.2

/-- Currying identifies one flat table over global decision keys with a pure
contingent-plan profile. -/
def decisionTableEquiv (G : ObservedGame N U) :
    ((key : G.DecisionKey) →
      G.DecisionValue key) ≃
      G.PureProfile :=
  Equiv.piCurry fun i information =>
    G.InfoAction i information

/-- Flatten a behavioral profile into the independent law family indexed by
global decision keys. -/
def BehavioralProfile.decisionLaw
    (G : ObservedGame N U)
    (profile : G.BehavioralProfile)
    (key : G.DecisionKey) :
    PMF (G.DecisionValue key) :=
  profile key.1 key.2

/-- Every player decision on every continuation of `current` has its key in
`remaining`.

This future-closed invariant is stronger than availability only at the
current endpoint.  The strength makes it compose cleanly through chance and
player steps. -/
def FutureDecisionKeysAvailable
    (G : ObservedGame N U)
    (current :
      G.base.toArena.HistoryFrom G.base.init)
    (remaining : Finset G.DecisionKey) : Prop :=
  ∀ {finish : G.base.State}
    (suffix :
      G.base.toArena.History current.1 finish)
    (i : N)
    (hmover : G.base.mover finish = some i)
    (hnonterminal : ¬ G.base.isTerminal finish),
    (⟨i,
      G.infoAt
        ⟨finish, current.2.append suffix⟩
        i hmover hnonterminal⟩ : G.DecisionKey) ∈ remaining

namespace FutureDecisionKeysAvailable

variable {G : ObservedGame N U}

/-- With a finite global decision-key type, all keys are initially
available. -/
theorem univ [Fintype G.DecisionKey]
    (current :
      G.base.toArena.HistoryFrom G.base.init) :
    G.FutureDecisionKeysAvailable current Finset.univ := by
  intro finish suffix i hmover hnonterminal
  simp

/-- A chance step consumes no strategic query key. -/
theorem afterChance
    {current :
      G.base.toArena.HistoryFrom G.base.init}
    {remaining : Finset G.DecisionKey}
    (havailable :
      G.FutureDecisionKeysAvailable current remaining)
    (action : G.base.Action current.1) :
    G.FutureDecisionKeysAvailable
      ⟨G.base.next current.1 action,
        current.2.snoc action⟩
      remaining := by
  intro finish suffix i hmover hnonterminal
  let extended :
      G.base.toArena.History current.1 finish :=
    (Arena.History.nil.snoc action).append suffix
  have hmem :=
    havailable extended i hmover hnonterminal
  simpa [extended, ← Arena.History.append_assoc] using hmem

/-- A player step consumes exactly its current decision key.

No absent-mindedness proves that this key cannot occur at any later player
history on the continuation. -/
theorem afterPlayer
    [DecidableEq G.DecisionKey]
    (hnoAbsent : G.NoAbsentMindedness)
    {current :
      G.base.toArena.HistoryFrom G.base.init}
    {remaining : Finset G.DecisionKey}
    (havailable :
      G.FutureDecisionKeysAvailable current remaining)
    (i : N)
    (hmover : G.base.mover current.1 = some i)
    (hnonterminal : ¬ G.base.isTerminal current.1)
    (action : G.base.Action current.1) :
    G.FutureDecisionKeysAvailable
      ⟨G.base.next current.1 action,
        current.2.snoc action⟩
      (remaining.erase
        (⟨i, G.infoAt current i hmover hnonterminal⟩ :
          G.DecisionKey)) := by
  intro finish suffix j hfinish hfinish_nonterminal
  apply Finset.mem_erase.mpr
  constructor
  · intro heq
    have hplayer : j = i :=
      (Sigma.mk.inj_iff.mp heq).1
    subst j
    have hinfo :
        G.infoAt
            ⟨finish,
              (current.2.snoc action).append suffix⟩
            i hfinish hfinish_nonterminal =
          G.infoAt current i hmover hnonterminal :=
      eq_of_heq (Sigma.mk.inj_iff.mp heq).2
    exact
      (hnoAbsent i current hmover action
        finish suffix hfinish hfinish_nonterminal) hinfo.symm
  · let extended :
        G.base.toArena.History current.1 finish :=
      (Arena.History.nil.snoc action).append suffix
    have hmem :=
      havailable extended j hfinish hfinish_nonterminal
    simpa [extended, ← Arena.History.append_assoc] using hmem

/-- The current player key is available by taking the empty
continuation. -/
theorem current
    {current :
      G.base.toArena.HistoryFrom G.base.init}
    {remaining : Finset G.DecisionKey}
    (havailable :
      G.FutureDecisionKeysAvailable current remaining)
    (i : N)
    (hmover : G.base.mover current.1 = some i)
    (hnonterminal : ¬ G.base.isTerminal current.1) :
    (⟨i, G.infoAt current i hmover hnonterminal⟩ :
      G.DecisionKey) ∈ remaining := by
  simpa using
    havailable
      (Arena.History.nil :
        G.base.toArena.History current.1 current.1)
      i hmover hnonterminal

end FutureDecisionKeysAvailable

namespace FiniteInformationHypotheses

variable {G : ObservedGame N U}
variable [Fintype N]
variable [Fintype G.DecisionKey]

/-- The flat independent law on all player/information keys is exactly the
existing two-level law that first samples players independently and then
samples every player's information-state actions independently. -/
theorem map_fintypePi_decisionLaw
    (h : G.FiniteInformationHypotheses)
    (profile : G.BehavioralProfile) :
      (PMF.fintypePi
        (profile.decisionLaw G)).map
          G.decisionTableEquiv =
      (h.behavioralToMixedProfile profile).pureProfileLaw G := by
  classical
  letI (i : N) : Finite (G.InfoState i) :=
    h.finiteInfoState i
  letI (i : N) : Fintype (G.InfoState i) :=
    Fintype.ofFinite (G.InfoState i)
  ext pureProfile
  rw [PMF.map_equiv_apply,
    PMF.fintypePi_apply]
  unfold MixedProfile.pureProfileLaw
  calc
    (∏ key : G.DecisionKey,
        profile.decisionLaw G key
          (G.decisionTableEquiv.symm
            pureProfile key)) =
        ∏ i : N,
          ∏ information : G.InfoState i,
            profile i information
              (pureProfile i information) := by
      rw [show
        (Finset.univ : Finset G.DecisionKey) =
          (Finset.univ : Finset N).sigma
            (fun i =>
              (Finset.univ :
                Finset (G.InfoState i))) by
          ext key
          simp]
      rw [Finset.prod_sigma]
      apply Finset.prod_congr rfl
      intro i _
      apply Finset.prod_congr rfl
      intro information _
      rfl
    _ = ∏ i : N,
          (h.behavioralToMixedProfile profile i)
            (pureProfile i) := by
      apply Finset.prod_congr rfl
      intro i _
      simp only [behavioralToMixedProfile]
      exact
        (PMF.fintypePi_apply
          (profile i) (pureProfile i)).symm
    _ = PMF.fintypePi
          (h.behavioralToMixedProfile profile)
          pureProfile :=
      (PMF.fintypePi_apply
        (h.behavioralToMixedProfile profile)
        pureProfile).symm

end FiniteInformationHypotheses

namespace FiniteNoAbsentMindednessHypotheses

variable {G : ObservedGame N U}
variable [Fintype N] [DecidableEq N]
variable [Fintype G.DecisionKey]

/-- Compatibility wrapper around the finite-information table-law theorem. -/
theorem map_fintypePi_decisionLaw
    (h : G.FiniteNoAbsentMindednessHypotheses)
    (profile : G.BehavioralProfile) :
      (PMF.fintypePi
        (profile.decisionLaw G)).map
          G.decisionTableEquiv =
      (h.behavioralToMixedProfile profile).pureProfileLaw G := by
  let hfinite := h.toFiniteInformationHypotheses
  simpa [hfinite,
    behavioralToMixedProfile,
    behavioralToMixedStrategy,
    toFiniteInformationHypotheses] using
      hfinite.map_fintypePi_decisionLaw profile

end FiniteNoAbsentMindednessHypotheses

namespace FiniteKuhnHypotheses

variable {G : ObservedGame N U}
variable [Fintype N] [DecidableEq N]
variable [Fintype G.DecisionKey]

/-- Compatibility wrapper for the stronger traditional Kuhn hypotheses. -/
theorem map_fintypePi_decisionLaw
    (h : G.FiniteKuhnHypotheses)
    (profile : G.BehavioralProfile) :
      (PMF.fintypePi
        (profile.decisionLaw G)).map
          G.decisionTableEquiv =
      (h.behavioralToMixedProfile profile).pureProfileLaw G := by
  let hweak :=
    h.toFiniteNoAbsentMindednessHypotheses
  simpa [hweak,
    FiniteNoAbsentMindednessHypotheses.behavioralToMixedProfile,
    FiniteNoAbsentMindednessHypotheses.behavioralToMixedStrategy,
    FiniteKuhnHypotheses.behavioralToMixedProfile,
    FiniteKuhnHypotheses.behavioralToMixedStrategy,
    FiniteKuhnHypotheses.toFiniteNoAbsentMindednessHypotheses] using
      hweak.map_fintypePi_decisionLaw profile

end FiniteKuhnHypotheses

end ExtensiveGame.ObservedGame
