/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Inverse
import EconCSLib.Math.Probability.PMF.Equiv
import EconCSLib.GameTheory.ExtensiveGame.Execution.StochasticExecution
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.Chance

Normalized chance kernels for history-indexed observed extensive games.

`ObservedChanceGame` wraps an `ObservedGame` with a `PMF` on the legal action
type at every nonterminal history whose mover is `none`.  Since the kernel is a
`PMF`, total probability mass is one by construction.

A strict chance-game isomorphism extends the strict structural
`ObservedGame.Iso`.  In addition to preserving observations, public states,
information actions, terminal payoffs, and presentation-designated
continuation roots, it requires the source chance law pushed through the
dependent action equivalence to equal the target chance law exactly.

## Main definitions

* `ObservedChanceGame` — an observed EFG with normalized chance kernels.
* `ObservedChanceGame.withChanceKernel` — attach an explicitly supplied
  chance law to any observed presentation.
* `ObservedChanceGame.completeInformationPresentation` — compose the
  complete-information presentation with an explicit chance law.
* `ObservedChanceGame.chanceSuccessorKernel` — the induced distribution on
  complete successor histories.
* `ObservedChanceGame.Iso` — strict observed-EFG isomorphism preserving chance
  laws.
* `ObservedChanceGame.Iso.refl`, `symm`, and `trans` — identity, inverse, and
  composition of strict chance isomorphisms.

## Main results

* `Iso.map_chanceSuccessorKernel` — strict naturality of the successor-history
  distribution.
-/

namespace ExtensiveGame

universe uN uU uA uS uO uI uP

/-- A history-indexed observed EFG equipped with a normalized kernel at every
chance history. -/
structure ObservedChanceGame (N : Type uN) (U : Type uU) where
  /-- The strategic, payoff, observation, public-state, information, and
  designated-continuation-root structure. -/
  observed : ObservedGame.{uN, uU, uA, uS, uO, uI, uP} N U
  /-- The normalized distribution on legal actions at each chance history. -/
  chanceKernel :
    (h : observed.base.toArena.HistoryFrom observed.base.init) →
      observed.base.isChanceState h.1 →
      PMF (observed.base.Action h.1)

namespace ObservedChanceGame

variable {N : Type uN} {U : Type uU}

/-- Attach an explicitly supplied normalized chance kernel to an observed
game.

The constructor performs no inference from movers, actions, or payoffs: the
caller remains responsible for every chance law. -/
abbrev withChanceKernel
    (observed : ObservedGame N U)
    (chanceKernel :
      (h : observed.base.toArena.HistoryFrom observed.base.init) →
        observed.base.isChanceState h.1 →
        PMF (observed.base.Action h.1)) :
    ObservedChanceGame N U where
  observed := observed
  chanceKernel := chanceKernel

/-- Canonical complete-information observation of an ordinary extensive game,
with independently selected presentation roots and an explicitly supplied
chance kernel. -/
abbrev completeInformationPresentation
    (base : ExtensiveGame N U)
    (roots : ObservedGame.ContinuationRootPresentation base)
    (chanceKernel :
      (h : base.toArena.HistoryFrom base.init) →
        base.isChanceState h.1 →
        PMF (base.Action h.1)) :
    ObservedChanceGame N U :=
  withChanceKernel
    (ObservedGame.completeInformationPresentation base roots)
    chanceKernel

@[simp]
theorem withChanceKernel_observed
    (observed : ObservedGame N U)
    (chanceKernel :
      (h : observed.base.toArena.HistoryFrom observed.base.init) →
        observed.base.isChanceState h.1 →
        PMF (observed.base.Action h.1)) :
    (withChanceKernel observed chanceKernel).observed = observed :=
  rfl

@[simp]
theorem withChanceKernel_chanceKernel
    (observed : ObservedGame N U)
    (chanceKernel :
      (h : observed.base.toArena.HistoryFrom observed.base.init) →
        observed.base.isChanceState h.1 →
        PMF (observed.base.Action h.1))
    (history : observed.base.toArena.HistoryFrom observed.base.init)
    (hchance : observed.base.isChanceState history.1) :
    (withChanceKernel observed chanceKernel).chanceKernel history hchance =
      chanceKernel history hchance :=
  rfl

@[simp]
theorem completeInformationPresentation_observed
    (base : ExtensiveGame N U)
    (roots : ObservedGame.ContinuationRootPresentation base)
    (chanceKernel :
      (h : base.toArena.HistoryFrom base.init) →
        base.isChanceState h.1 →
        PMF (base.Action h.1)) :
    (completeInformationPresentation base roots chanceKernel).observed =
      ObservedGame.completeInformationPresentation base roots :=
  rfl

@[simp]
theorem completeInformationPresentation_chanceKernel
    (base : ExtensiveGame N U)
    (roots : ObservedGame.ContinuationRootPresentation base)
    (chanceKernel :
      (h : base.toArena.HistoryFrom base.init) →
        base.isChanceState h.1 →
        PMF (base.Action h.1))
    (history : base.toArena.HistoryFrom base.init)
    (hchance : base.isChanceState history.1) :
    (completeInformationPresentation base roots chanceKernel).chanceKernel
        history hchance =
      chanceKernel history hchance :=
  rfl

/-- The distribution of complete successor histories induced by a chance
kernel. -/
noncomputable def chanceSuccessorKernel (G : ObservedChanceGame N U)
    (h : G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hchance : G.observed.base.isChanceState h.1) :
    PMF (G.observed.base.toArena.HistoryFrom G.observed.base.init) :=
  (G.chanceKernel h hchance).map fun action =>
    ⟨G.observed.base.next h.1 action, h.2.snoc action⟩

/-- A chance successor kernel has total probability mass one. -/
@[simp]
theorem chanceSuccessorKernel_tsum (G : ObservedChanceGame N U)
    (h : G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hchance : G.observed.base.isChanceState h.1) :
    ∑' nextHistory, G.chanceSuccessorKernel h hchance nextHistory = 1 :=
  PMF.tsum_coe (G.chanceSuccessorKernel h hchance)

/-- Characterization of the positive-probability successor histories. -/
theorem mem_support_chanceSuccessorKernel_iff
    (G : ObservedChanceGame N U)
    (h : G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hchance : G.observed.base.isChanceState h.1)
    (nextHistory :
      G.observed.base.toArena.HistoryFrom G.observed.base.init) :
    nextHistory ∈ (G.chanceSuccessorKernel h hchance).support ↔
      ∃ action ∈ (G.chanceKernel h hchance).support,
        (⟨G.observed.base.next h.1 action, h.2.snoc action⟩ :
          G.observed.base.toArena.HistoryFrom G.observed.base.init) =
          nextHistory :=
  by
    simp [chanceSuccessorKernel]

/-- A stochastic history policy is chance-consistent when it uses the
game-specified chance kernel at every chance history.  The policy remains free
to encode strategic or administrative choices at player-controlled
histories. -/
def ChanceConsistent (G : ObservedChanceGame N U)
    (policy :
      G.observed.base.toArena.StochasticHistoryPolicy
        G.observed.base.init) : Prop :=
  ∀ (h : G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hnonterminal : ¬ G.observed.base.isTerminal h.1)
    (hmover : G.observed.base.mover h.1 = none),
    policy h hnonterminal =
      G.chanceKernel h ⟨hmover, hnonterminal⟩

/-- A strict observed-EFG isomorphism maps chance histories to chance
histories. -/
def mapChanceState {G H : ObservedGame N U} (e : G.Iso H)
    (h : G.base.toArena.HistoryFrom G.base.init)
    (hchance : G.base.isChanceState h.1) :
    H.base.isChanceState (e.historyIso.stateEquiv h).1 := by
  constructor
  · calc
      H.base.mover (e.historyIso.stateEquiv h).1 =
          G.base.mover h.1 := e.map_mover h
      _ = none := hchance.1
  · intro hterminal
    exact hchance.2 ((e.historyIso.isTerminal_iff h).mpr hterminal)

/-- A strict structural isomorphism of observed EFGs that also preserves every
chance kernel exactly under the dependent action equivalence. -/
structure Iso (G H : ObservedChanceGame N U) where
  /-- Strict isomorphism of observations, public states, information actions,
  payoffs, and presentation-designated continuation roots. -/
  observedIso : G.observed.Iso H.observed
  /-- Chance laws commute exactly with action relabeling. -/
  map_chanceKernel :
    ∀ (h : G.observed.base.toArena.HistoryFrom G.observed.base.init)
      (hchance : G.observed.base.isChanceState h.1),
      (G.chanceKernel h hchance).map
          (observedIso.historyIso.actionEquiv h) =
        H.chanceKernel
          (observedIso.historyIso.stateEquiv h)
          (mapChanceState observedIso h hchance)

namespace Iso

variable {G H : ObservedChanceGame N U}

/-- Chance-game isomorphisms are determined by their observed structural
isomorphism; chance-kernel naturality is propositional. -/
@[ext]
theorem ext (e f : G.Iso H)
    (hObserved : e.observedIso = f.observedIso) :
    e = f := by
  cases e
  cases f
  cases hObserved
  rfl

private theorem chanceKernel_map_cast
    (G : ObservedChanceGame N U)
    {first second :
      G.observed.base.toArena.HistoryFrom G.observed.base.init}
    (hhistory : first = second)
    (hfirst : G.observed.base.isChanceState first.1)
    (hsecond : G.observed.base.isChanceState second.1) :
    (G.chanceKernel first hfirst).map
        (Equiv.cast
          (congrArg G.observed.base.unfold.Action hhistory)) =
      G.chanceKernel second hsecond := by
  subst second
  have hchance : hsecond = hfirst :=
    Subsingleton.elim _ _
  cases hchance
  simpa using PMF.map_id (G.chanceKernel first hfirst)

/-- Identity strict isomorphism of an observed chance EFG. -/
def refl (G : ObservedChanceGame N U) : G.Iso G where
  observedIso := ObservedGame.Iso.refl G.observed
  map_chanceKernel := by
    intro h hchance
    simpa using PMF.map_id (G.chanceKernel h hchance)

/-- Compose strict observed chance-EFG isomorphisms. -/
def trans {K : ObservedChanceGame N U}
    (e : G.Iso H) (f : H.Iso K) :
    G.Iso K where
  observedIso := e.observedIso.trans f.observedIso
  map_chanceKernel := by
    intro history hchance
    let middleChance :=
      mapChanceState e.observedIso history hchance
    change
      (G.chanceKernel history hchance).map
          ((fun action =>
            f.observedIso.historyIso.actionEquiv
              (e.observedIso.historyIso.stateEquiv history)
              action) ∘
            e.observedIso.historyIso.actionEquiv history) =
        K.chanceKernel
          (f.observedIso.historyIso.stateEquiv
            (e.observedIso.historyIso.stateEquiv history))
          _
    rw [← PMF.map_comp]
    rw [e.map_chanceKernel history hchance]
    exact
      f.map_chanceKernel
        (e.observedIso.historyIso.stateEquiv history)
        middleChance

/-- Identity is a left unit for observed chance-game isomorphism
composition. -/
@[simp]
theorem refl_trans (e : G.Iso H) :
    (refl G).trans e = e := by
  apply Iso.ext
  exact ObservedGame.Iso.refl_trans e.observedIso

/-- Identity is a right unit for observed chance-game isomorphism
composition. -/
@[simp]
theorem trans_refl (e : G.Iso H) :
    e.trans (refl H) = e := by
  apply Iso.ext
  exact ObservedGame.Iso.trans_refl e.observedIso

/-- Composition of observed chance-game isomorphisms is associative. -/
theorem trans_assoc {K L : ObservedChanceGame N U}
    (e : G.Iso H) (f : H.Iso K) (g : K.Iso L) :
    (e.trans f).trans g = e.trans (f.trans g) := by
  apply Iso.ext
  exact ObservedGame.Iso.trans_assoc
    e.observedIso f.observedIso g.observedIso

/-- Reverse a strict observed chance-EFG isomorphism. -/
noncomputable def symm (e : G.Iso H) : H.Iso G where
  observedIso := e.observedIso.symm
  map_chanceKernel := by
    intro history hchance
    let inverseAction :=
      (e.observedIso.symm).historyIso.actionEquiv history
    apply (PMF.mapEquiv inverseAction.symm).injective
    change
      ((H.chanceKernel history hchance).map inverseAction).map
          inverseAction.symm =
        (G.chanceKernel
          ((e.observedIso.symm).historyIso.stateEquiv history)
          _).map inverseAction.symm
    rw [PMF.map_comp]
    have hinverse :
        (inverseAction.symm : _ → _) ∘
            (inverseAction : _ → _) =
          id := by
      funext action
      exact inverseAction.symm_apply_apply action
    rw [hinverse, PMF.map_id]
    let sourceHistory :=
      e.observedIso.historyIso.stateEquiv.symm history
    let hsourceChance :=
      mapChanceState e.observedIso.symm history hchance
    have hforward :=
      e.map_chanceKernel sourceHistory hsourceChance
    have hhistory :
        e.observedIso.historyIso.stateEquiv sourceHistory =
          history :=
      e.observedIso.historyIso.stateEquiv.apply_symm_apply history
    let htargetChance :=
      mapChanceState e.observedIso sourceHistory hsourceChance
    have hinverseAction :
        (inverseAction.symm : _ → _) =
          (Equiv.cast
              (congrArg H.observed.base.unfold.Action hhistory)) ∘
            e.observedIso.historyIso.actionEquiv sourceHistory := by
      funext action
      rfl
    calc
      H.chanceKernel history hchance =
          (H.chanceKernel
              (e.observedIso.historyIso.stateEquiv sourceHistory)
              htargetChance).map
            (Equiv.cast
              (congrArg H.observed.base.unfold.Action hhistory)) := by
        exact
          (chanceKernel_map_cast H hhistory
            htargetChance hchance).symm
      _ = ((G.chanceKernel sourceHistory hsourceChance).map
            (e.observedIso.historyIso.actionEquiv sourceHistory)).map
          (Equiv.cast
            (congrArg H.observed.base.unfold.Action hhistory)) := by
        rw [hforward]
      _ = (G.chanceKernel sourceHistory hsourceChance).map
          ((Equiv.cast
              (congrArg H.observed.base.unfold.Action hhistory)) ∘
            e.observedIso.historyIso.actionEquiv sourceHistory) := by
        rw [PMF.map_comp]
      _ = (G.chanceKernel sourceHistory hsourceChance).map
          inverseAction.symm := by
        rw [hinverseAction]
        rfl

/-- Strict chance isomorphisms commute with the complete successor-history
distribution. -/
theorem map_chanceSuccessorKernel (e : G.Iso H)
    (h : G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hchance : G.observed.base.isChanceState h.1) :
    (G.chanceSuccessorKernel h hchance).map
        e.observedIso.historyIso.stateEquiv =
      H.chanceSuccessorKernel
        (e.observedIso.historyIso.stateEquiv h)
        (mapChanceState e.observedIso h hchance) := by
  let sourceSuccessor :
      G.observed.base.Action h.1 →
        G.observed.base.toArena.HistoryFrom G.observed.base.init :=
    fun action =>
      ⟨G.observed.base.next h.1 action, h.2.snoc action⟩
  let targetSuccessor :
      H.observed.base.Action
          (e.observedIso.historyIso.stateEquiv h).1 →
        H.observed.base.toArena.HistoryFrom H.observed.base.init :=
    fun action =>
      ⟨H.observed.base.next
          (e.observedIso.historyIso.stateEquiv h).1 action,
        (e.observedIso.historyIso.stateEquiv h).2.snoc action⟩
  calc
    (G.chanceSuccessorKernel h hchance).map
        e.observedIso.historyIso.stateEquiv =
      (G.chanceKernel h hchance).map
        (e.observedIso.historyIso.stateEquiv ∘ sourceSuccessor) := by
          simpa [chanceSuccessorKernel, sourceSuccessor] using
            (PMF.map_comp sourceSuccessor
              (G.chanceKernel h hchance)
              e.observedIso.historyIso.stateEquiv)
    _ = (G.chanceKernel h hchance).map
        (targetSuccessor ∘
          e.observedIso.historyIso.actionEquiv h) := by
          apply congrArg (fun f => (G.chanceKernel h hchance).map f)
          funext action
          exact e.observedIso.historyIso.map_next h action
    _ = ((G.chanceKernel h hchance).map
          (e.observedIso.historyIso.actionEquiv h)).map
            targetSuccessor := by
          exact
            (PMF.map_comp
              (e.observedIso.historyIso.actionEquiv h)
              (G.chanceKernel h hchance)
              targetSuccessor).symm
        _ = (H.chanceKernel
          (e.observedIso.historyIso.stateEquiv h)
          (mapChanceState e.observedIso h hchance)).map
            targetSuccessor := by
          rw [e.map_chanceKernel h hchance]
    _ = H.chanceSuccessorKernel
        (e.observedIso.historyIso.stateEquiv h)
        (mapChanceState e.observedIso h hchance) := rfl

end Iso

end ObservedChanceGame

end ExtensiveGame
