/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.StochasticNaturality
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled

/-!
# Payoff-free discrete chance and bounded history laws

`DiscreteControlledObservedChanceGame` attaches normalized, countably
supported `PMF` chance kernels to a payoff-free observed controlled game.
It stores no payoff, root selection, finiteness, recall, or objective.

The maximal semantic object in this finite import tier is the bounded PMF on
complete occurrence-sensitive histories. Full measure-valued path laws and
their downstream interpretation hierarchy live in `ControlledLaw`, so finite
clients do not acquire the infinite execution stack.
-/

namespace ExtensiveGame

universe uN uA uS uO uI uP

/-- A payoff-free observed game with discrete, countably supported chance
kernels. -/
structure DiscreteControlledObservedChanceGame
    (N : Type uN) where
  /-- Payoff-free observed strategic carrier. -/
  observed :
    ControlledObservedGame.{uN, uA, uS, uO, uI, uP} N
  /-- Normalized law on legal actions at every chance history. -/
  chanceKernel :
    (history : observed.base.History) →
      observed.base.isChanceState history.1 →
        PMF (observed.base.Action history.1)

namespace DiscreteControlledObservedChanceGame

variable {N : Type*}
  (G : DiscreteControlledObservedChanceGame N)

/-- Attach a discrete chance kernel to a payoff-free observation carrier. -/
abbrev withChanceKernel
    (observed : ControlledObservedGame N)
    (chanceKernel :
      (history : observed.base.History) →
        observed.base.isChanceState history.1 →
          PMF (observed.base.Action history.1)) :
    DiscreteControlledObservedChanceGame N where
  observed := observed
  chanceKernel := chanceKernel

/-- Behavioral plans indexed only by decision information. -/
abbrev BehavioralStrategy (i : N) :=
  (information : G.observed.InfoState i) →
    PMF (G.observed.InfoAction i information)

/-- One payoff-free behavioral plan per player. -/
abbrev BehavioralProfile :=
  (i : N) → G.BehavioralStrategy i

/-- Unilateral update of a payoff-free behavioral profile. -/
def BehavioralProfile.deviate [DecidableEq N]
    (profile : G.BehavioralProfile) (who : N)
    (deviation : G.BehavioralStrategy who) :
    G.BehavioralProfile :=
  Function.update profile who deviation

/-- Concrete legal-action law at one represented player decision. -/
noncomputable def BehavioralStrategy.actionLawAt
    {i : N} (strategy : G.BehavioralStrategy i)
    (history : G.observed.base.History)
    (hmover :
      G.observed.base.mover history.1 = some i) :
    PMF (G.observed.base.Action history.1) :=
  (strategy
    (G.observed.infoAt history i hmover)).map
      (G.observed.actionEquiv history i hmover)

/-- Stochastic history policy induced jointly by strategic and chance laws. -/
noncomputable def BehavioralProfile.toHistoryPolicy
    (profile : G.BehavioralProfile) :
    G.observed.base.toArena.StochasticHistoryPolicy
      G.observed.base.init :=
  fun history hnonterminal =>
    match hmover : G.observed.base.mover history.1 with
    | some i =>
        (profile i).actionLawAt G history hmover
    | none =>
        G.chanceKernel history ⟨hmover, hnonterminal⟩

/-- At a represented player decision, the induced stochastic history policy
is the mover's concrete behavioral action law. -/
theorem BehavioralProfile.toHistoryPolicy_of_mover
    (profile : G.BehavioralProfile)
    (history : G.observed.base.History)
    (hnonterminal :
      ¬ G.observed.base.isTerminal history.1)
    (i : N)
    (hmover : G.observed.base.mover history.1 = some i) :
    profile.toHistoryPolicy G history hnonterminal =
      (profile i).actionLawAt G history hmover := by
  rw [BehavioralProfile.toHistoryPolicy]
  split
  · rename_i j hj
    have hji : j = i :=
      Option.some.inj (hj.symm.trans hmover)
    subst j
    rfl
  · rename_i hnone
    rw [hmover] at hnone
    contradiction

/-- At a chance history, the induced stochastic history policy is exactly
the stored discrete chance kernel. -/
theorem BehavioralProfile.toHistoryPolicy_of_chance
    (profile : G.BehavioralProfile)
    (history : G.observed.base.History)
    (hnonterminal :
      ¬ G.observed.base.isTerminal history.1)
    (hmover : G.observed.base.mover history.1 = none) :
    profile.toHistoryPolicy G history hnonterminal =
      G.chanceKernel history ⟨hmover, hnonterminal⟩ := by
  rw [BehavioralProfile.toHistoryPolicy]
  split
  · rename_i i hi
    rw [hmover] at hi
    contradiction
  · rfl

/-- Bounded complete-history PMF for the discrete behavioral model. -/
noncomputable def behavioralHistoryLaw
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (profile : G.BehavioralProfile)
    (current : G.observed.base.History)
    (fuel : ℕ) :
    PMF G.observed.base.History :=
  G.observed.base.toArena.stochasticHistoryPMFFrom
    (profile.toHistoryPolicy G) current fuel

end DiscreteControlledObservedChanceGame

namespace DiscreteControlledObservedChanceGame

universe uStrategy

variable {N : Type*}

/-! ## Payoff-free bounded complete-history semantics -/

/-- A strategy-indexed bounded complete-history PMF semantics.

The semantic object is the full occurrence-sensitive history, not merely its
endpoint state. The structure stores no payoff, objective, or root set. -/
structure BoundedCompleteHistoryLawSemantics
    (G : DiscreteControlledObservedChanceGame N) where
  /-- One strategy carrier per player. -/
  Strategy : N → Type uStrategy
  /-- Complete-history law from every current history and fuel bound. -/
  historyLaw :
    (profile : ∀ i, Strategy i) →
      G.observed.base.History → ℕ →
        PMF G.observed.base.History

namespace BoundedCompleteHistoryLawSemantics

variable {G : DiscreteControlledObservedChanceGame N}

/-- Profiles for one bounded complete-history semantic model. -/
abbrev Profile (S : G.BoundedCompleteHistoryLawSemantics) :=
  ∀ i, S.Strategy i

/-- Equality of bounded occurrence-sensitive complete-history laws. -/
def CompleteHistoryLawEquivalentAt
    (S T : G.BoundedCompleteHistoryLawSemantics)
    (source : S.Profile) (target : T.Profile)
    (current : G.observed.base.History)
    (fuel : ℕ) : Prop :=
  S.historyLaw source current fuel =
    T.historyLaw target current fuel

/-- One-way realization of every bounded complete-history law.

The playerwise strategy map gives a source-deviation map. Reverse target
deviation coverage remains a separate property. -/
