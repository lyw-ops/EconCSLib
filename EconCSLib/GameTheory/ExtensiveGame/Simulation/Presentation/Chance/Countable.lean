/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.Measurable
import EconCSLib.Math.Probability.PMF.ToMeasure

/-!
# Presentation.Chance.Countable — countable-discrete analytic presentations

This module constructs the explicit
`ObservedChanceGame.AnalyticPresentation` certificate for a common, strictly
bounded class of models: complete histories and the total carrier of
history-local base actions are countable. The tagged information/action
carriers, concrete action bundle, and every finite event-prefix carrier are
then countable by construction. The ambient player type and unreachable
declared information/action fibers need not be countable.

The constructor uses disjoint information tags:

* `terminal`, for terminal histories whose mover is `none`;
* `player reachableInformation`, retaining an original
  `ObservedGame.InfoState` witnessed by a player-controlled history;
* `chance history hchance`, retaining the complete chance history.

Abstract actions depend on the tag. Player tags carry the original dependent
`InfoAction`; chance tags carry the local base action; terminal tags carry no
action. Behavioral and chance PMFs are mapped into this common tagged sigma
carrier.

The fixed realization kernel is zero at terminal prefixes. At a nonterminal
prefix it is Dirac at a legal local action. A matching tag uses
`ObservedGame.actionEquiv` or the identity chance action. A mismatched tag uses
one classically chosen legal fallback. Mismatched tags have zero mass under
the canonical policy; the fallback exists only to keep the fixed realization
globally normalized at every nonterminal input.

Terminality is tested before the mover branch. This matches the core contract
that information states and abstract actions are available only at genuine
nonterminal decisions, even though the base `ExtensiveGame` interface permits
a terminal state to retain a player label. Such labels are ignored by the
presentation and do not create spurious behavioral-strategy coordinates.

All measurable spaces introduced here are discrete top spaces. Countability
of the final carriers makes arbitrary maps and measure families from those
carriers measurable. Terminal branching is classical inside these
noncomputable kernels, so no terminal-decidability typeclass is required by
the presentation. No analogous constructor is claimed for arbitrary
uncountable observed games.
-/

open MeasureTheory ProbabilityTheory

namespace ExtensiveGame.ObservedChanceGame

universe uN uU

variable {N : Type uN} {U : Type uU}

/-- Total carrier of original player-information points. This carrier need not
be countable: the canonical presentation retains only its reachable
subtype. -/
abbrev PlayerInformationPoint (G : ObservedChanceGame N U) :=
  Σ i : N, G.observed.InfoState i

/-- An original player-information point is reachable when some
player-controlled complete history maps to it. -/
def IsReachablePlayerInformation
    (G : ObservedChanceGame N U)
    (information : PlayerInformationPoint G) : Prop :=
  ∃ (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hmover :
      G.observed.base.mover history.1 = some information.1)
    (hnonterminal :
      ¬ G.observed.base.isTerminal history.1),
    G.observed.infoAt history information.1 hmover hnonterminal =
      information.2

/-- Proof-carrying carrier of reachable original player-information points. -/
abbrev ReachablePlayerInformation (G : ObservedChanceGame N U) :=
  {information : PlayerInformationPoint G //
    IsReachablePlayerInformation G information}

/-- A player-controlled history viewed as a history together with its uniquely
determined mover. -/
abbrev PlayerHistory (G : ObservedChanceGame N U) :=
  Σ history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init,
    {i : N //
      G.observed.base.mover history.1 = some i ∧
        ¬ G.observed.base.isTerminal history.1}

/-- The reachable player-information point represented by one
player-controlled complete history. -/
def reachablePlayerInformationAt
    (G : ObservedChanceGame N U)
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (i : N)
    (hmover : G.observed.base.mover history.1 = some i)
    (hnonterminal : ¬ G.observed.base.isTerminal history.1) :
    ReachablePlayerInformation G :=
  ⟨⟨i, G.observed.infoAt history i hmover hnonterminal⟩,
    ⟨history, hmover, hnonterminal, rfl⟩⟩

/-- Canonical disjoint information tags for the countable-discrete
presentation. -/
inductive CountableInformation (G : ObservedChanceGame N U)
  | terminal
  | player (information : ReachablePlayerInformation G)
  | chance
      (history :
        G.observed.base.toArena.HistoryFrom G.observed.base.init)
      (hchance : G.observed.base.isChanceState history.1)

namespace CountableInformation

/-- Abstract action type associated to one canonical information tag. -/
def Action
    {G : ObservedChanceGame N U} :
    CountableInformation G → Type _
  | .terminal => Empty
  | .player information =>
      G.observed.InfoAction information.1.1 information.1.2
  | .chance history _hchance =>
      G.observed.base.Action history.1

end CountableInformation

/-- Common tagged abstract-action carrier used by the countable-discrete
presentation. -/
abbrev CountableAction (G : ObservedChanceGame N U) :=
  Σ information : CountableInformation G, information.Action

/-- Total carrier of original dependent player-information actions. -/
abbrev PlayerInformationAction (G : ObservedChanceGame N U) :=
  Σ information : PlayerInformationPoint G,
    G.observed.InfoAction information.1 information.2

/-- Total carrier of complete-history/local-action pairs. Terminal histories
contribute no elements because their action fiber is empty. -/
abbrev CompleteHistoryAction (G : ObservedChanceGame N U) :=
  Σ history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init,
    G.observed.base.Action history.1

/-- Reachable player-information is countable as the image of the countable
carrier of player-controlled complete histories. -/
noncomputable instance instCountableReachablePlayerInformation
    (G : ObservedChanceGame N U)
    [Countable
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)] :
    Countable (ReachablePlayerInformation G) := by
  let forget :
      PlayerHistory G →
        G.observed.base.toArena.HistoryFrom G.observed.base.init :=
    fun playerHistory => playerHistory.1
  have forget_injective : Function.Injective forget := by
    intro first second heq
    rcases first with
      ⟨history, ⟨i, hmover, hnonterminal⟩⟩
    rcases second with
      ⟨targetHistory, ⟨j, targetMover, targetNonterminal⟩⟩
    change history = targetHistory at heq
    cases heq
    have hij : i = j :=
      Option.some.inj (hmover.symm.trans targetMover)
    subst j
    rfl
  letI : Countable (PlayerHistory G) :=
    forget_injective.countable
  let cover :
      PlayerHistory G → ReachablePlayerInformation G
    | ⟨history, ⟨i, hmover, hnonterminal⟩⟩ =>
        reachablePlayerInformationAt G history i hmover hnonterminal
  have hcover : Function.Surjective cover := by
    intro information
    rcases information with
      ⟨⟨i, playerInformation⟩,
        ⟨history, hmover, hnonterminal, hinformation⟩⟩
    refine
      ⟨⟨history, ⟨i, hmover, hnonterminal⟩⟩, ?_⟩
    apply Subtype.ext
    exact Sigma.ext rfl (heq_of_eq hinformation)
  exact hcover.countable

/-- The canonical information carrier is countable whenever complete
histories are countable. Unreachable original information points are not
included. Proof fields on player and chance tags do not enlarge the carrier. -/
noncomputable instance instCountableCountableInformation
    (G : ObservedChanceGame N U)
    [Countable
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)] :
    Countable (CountableInformation G) := by
  let cover :
      Unit ⊕
          ReachablePlayerInformation G ⊕
          {history :
              G.observed.base.toArena.HistoryFrom
                G.observed.base.init //
            G.observed.base.isChanceState history.1} →
        CountableInformation G
    | .inl _ => .terminal
    | .inr (.inl information) => .player information
    | .inr (.inr ⟨history, hchance⟩) =>
        .chance history hchance
  have hcover : Function.Surjective cover := by
    intro information
    cases information with
    | terminal =>
        exact ⟨.inl (), rfl⟩
    | player playerInformation =>
        exact ⟨.inr (.inl playerInformation), rfl⟩
    | chance history hchance =>
        exact ⟨.inr (.inr ⟨history, hchance⟩), rfl⟩
  exact hcover.countable

/-- Every dependent abstract-action fiber is countable when the total
complete-history-action carrier is countable. A reachable player action is
embedded through a witnessing history's `actionEquiv`; a chance action is
embedded directly. -/
noncomputable instance instCountableCountableInformationAction
    (G : ObservedChanceGame N U)
    [Countable (CompleteHistoryAction G)] :
    ∀ information : CountableInformation G,
      Countable information.Action
  | .terminal => by
      change Countable Empty
      infer_instance
  | .player information => by
      rcases information with
        ⟨⟨i, playerInformation⟩,
          ⟨history, hmover, hnonterminal, hinformation⟩⟩
      let transport :
          G.observed.InfoAction i playerInformation ≃
            G.observed.InfoAction i
              (G.observed.infoAt history i hmover hnonterminal) :=
        Equiv.cast
          (congrArg (G.observed.InfoAction i)
            hinformation.symm)
      exact
        (show Function.Injective
            (fun action : G.observed.InfoAction i playerInformation =>
              (⟨history,
                G.observed.actionEquiv history i hmover
                  hnonterminal
                  (transport action)⟩ :
                CompleteHistoryAction G)) by
          intro action₁ action₂ heq
          apply transport.injective
          apply
            (G.observed.actionEquiv history i hmover
              hnonterminal).injective
          exact eq_of_heq (Sigma.mk.inj_iff.mp heq).2).countable
  | .chance history _hchance => by
      exact
        (show Function.Injective
            (fun action : G.observed.base.Action history.1 =>
              (⟨history, action⟩ : CompleteHistoryAction G)) by
          intro action₁ action₂ heq
          cases heq
          rfl).countable

/-- The common tagged abstract-action sigma carrier is countable under the
minimal total-carrier countability hypotheses. -/
noncomputable instance instCountableCountableAction
    (G : ObservedChanceGame N U)
    [Countable
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    [Countable (CompleteHistoryAction G)] :
    Countable (CountableAction G) :=
  inferInstance

noncomputable instance instMeasurableSpaceCountableInformation
    (G : ObservedChanceGame N U) :
    MeasurableSpace (CountableInformation G) :=
  ⊤

noncomputable instance instMeasurableSpaceCountableAction
    (G : ObservedChanceGame N U) :
    MeasurableSpace (CountableAction G) :=
  ⊤

/-- The concrete complete-history action bundle is countable when histories
and their total local-action carrier are countable. -/
noncomputable instance instCountableAnalyticHistoryActionBundle
    (G : ObservedChanceGame N U)
    [Countable (CompleteHistoryAction G)] :
    Countable (AnalyticHistoryArena G).ActionBundle := by
  change Countable (CompleteHistoryAction G)
  infer_instance

/-- Concrete bundles in the discrete complete-history lift have measurable
singletons. -/
instance instMeasurableSingletonClassAnalyticHistoryActionBundle
    (G : ObservedChanceGame N U) :
    MeasurableSingletonClass (AnalyticHistoryArena G).ActionBundle where
  measurableSet_singleton _ :=
    MeasurableSpace.measurableSet_top

/-- One complete analytic path event has a measurable singleton. Mathlib has
the required product instance but no blanket sum-singleton instance, so the
optional action occurrence is handled by the measurable `inl`/`inr` images
directly. -/
instance instMeasurableSingletonClassAnalyticHistoryPathEvent
    (G : ObservedChanceGame N U) :
    MeasurableSingletonClass (AnalyticHistoryArena G).PathEvent where
  measurableSet_singleton event := by
    have hoptional :
        MeasurableSet
          ({event.2} :
            Set
              (Unit ⊕ (AnalyticHistoryArena G).ActionBundle)) := by
      cases event.2 with
      | inl value =>
          have heq :
              ({Sum.inl value} :
                  Set
                    (Unit ⊕
                      (AnalyticHistoryArena G).ActionBundle)) =
                Sum.inl '' ({value} : Set Unit) := by
            ext value
            simp
          rw [heq]
          exact
            MeasurableSet.inl_image
              (measurableSet_singleton value)
      | inr actionBundle =>
          have heq :
              ({Sum.inr actionBundle} :
                  Set
                    (Unit ⊕
                      (AnalyticHistoryArena G).ActionBundle)) =
                Sum.inr ''
                  ({actionBundle} :
                    Set (AnalyticHistoryArena G).ActionBundle) := by
            ext value
            simp
          rw [heq]
          exact
            MeasurableSet.inr_image
              (measurableSet_singleton actionBundle)
    have hevent :
        ({event.1} : Set (AnalyticHistoryArena G).State) ×ˢ
            ({event.2} :
              Set
                (Unit ⊕ (AnalyticHistoryArena G).ActionBundle)) =
          ({event} : Set (AnalyticHistoryArena G).PathEvent) :=
      Set.singleton_prod_singleton
    rw [← hevent]
    exact (measurableSet_singleton event.1).prod hoptional

/-- Complete optional-action path events are countable under the natural
history/action hypotheses. -/
noncomputable instance instCountableAnalyticHistoryPathEvent
    (G : ObservedChanceGame N U)
    [Countable
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    [Countable (CompleteHistoryAction G)] :
    Countable (AnalyticHistoryArena G).PathEvent := by
  change
    Countable
      ((G.observed.base.toArena.HistoryFrom
          G.observed.base.init) ×
        (Unit ⊕ (AnalyticHistoryArena G).ActionBundle))
  infer_instance

/-- Every finite event prefix is countable because it is a finite product of
countable complete path-event coordinates. -/
noncomputable instance instCountableAnalyticHistoryEventPrefix
    (G : ObservedChanceGame N U)
    [Countable
      (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
    [Countable (CompleteHistoryAction G)]
    (time : ℕ) :
    Countable ((AnalyticHistoryArena G).EventPrefix time) := by
  change
    Countable
      (∀ _index : Finset.Iic time,
        (AnalyticHistoryArena G).PathEvent)
  infer_instance

namespace CountablePresentation

variable (G : ObservedChanceGame N U)

/-- Canonical terminal/player/chance information at one complete history. -/
noncomputable def informationAtHistory
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init) :
    CountableInformation G := by
  classical
  exact
    if hterminal : G.observed.base.isTerminal history.1 then
      .terminal
    else
      match hmover : G.observed.base.mover history.1 with
      | some i =>
          .player
            (reachablePlayerInformationAt G history i hmover
              hterminal)
      | none =>
          .chance history ⟨hmover, hterminal⟩

@[simp]
theorem informationAtHistory_of_terminal
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hterminal : G.observed.base.isTerminal history.1) :
    informationAtHistory G history = .terminal := by
  simp [informationAtHistory, hterminal]

@[simp]
theorem informationAtHistory_of_terminal_of_no_mover
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hterminal : G.observed.base.isTerminal history.1)
    (_hmover : G.observed.base.mover history.1 = none) :
    informationAtHistory G history = .terminal := by
  exact informationAtHistory_of_terminal G history hterminal

@[simp]
theorem informationAtHistory_of_mover
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (i : N)
    (hmover : G.observed.base.mover history.1 = some i)
    (hnonterminal : ¬ G.observed.base.isTerminal history.1) :
    informationAtHistory G history =
      .player
        (reachablePlayerInformationAt G history i hmover
          hnonterminal) := by
  unfold informationAtHistory
  rw [dif_neg hnonterminal]
  split
  · rename_i j hj
    have hji : j = i :=
      Option.some.inj (hj.symm.trans hmover)
    subst j
    have hmoverProof : hj = hmover := Subsingleton.elim _ _
    cases hmoverProof
    rfl
  · rename_i hnone
    rw [hmover] at hnone
    contradiction

@[simp]
theorem informationAtHistory_of_chance
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hnonterminal :
      ¬ G.observed.base.isTerminal history.1)
    (hmover : G.observed.base.mover history.1 = none) :
    informationAtHistory G history =
      .chance history ⟨hmover, hnonterminal⟩ := by
  unfold informationAtHistory
  rw [dif_neg hnonterminal]
  split
  · rename_i i hi
    rw [hmover] at hi
    contradiction
  · rename_i hnone
    have hmoverProof : hnone = hmover := Subsingleton.elim _ _
    cases hmoverProof
    rfl

variable
  [Countable
    (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
  [Countable (CompleteHistoryAction G)]

/-- Fixed canonical measurable event-information statistic. -/
noncomputable def eventInformation :
    MeasurableKernelArena.EventInformation
      (AnalyticHistoryArena G) where
  Information := fun _time => CountableInformation G
  informationMeasurable := fun _time => inferInstance
  informationAt := fun time events =>
    informationAtHistory G
      (MeasurableKernelArena.latestEventState time events)
  informationAt_measurable := by
    intro time
    exact measurable_of_countable _

@[simp]
theorem eventInformation_apply
    (time : ℕ)
    (events : (AnalyticHistoryArena G).EventPrefix time) :
    (eventInformation G).informationAt time events =
      informationAtHistory G
        (MeasurableKernelArena.latestEventState time events) :=
  rfl

/-- Canonical injection of one original player information action into the
common tagged abstract-action carrier. -/
def playerAction
    (information : ReachablePlayerInformation G)
    (action :
      G.observed.InfoAction information.1.1 information.1.2) :
    CountableAction G :=
  ⟨.player information, action⟩

/-- Canonical injection of one local chance action into the common tagged
abstract-action carrier. -/
def chanceAction
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hchance : G.observed.base.isChanceState history.1)
    (action : G.observed.base.Action history.1) :
    CountableAction G :=
  ⟨.chance history hchance, action⟩

/-- One classically selected legal fallback action at a nonterminal complete
history. It is used only on mismatched abstract tags. -/
noncomputable def fallbackAction
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hnonterminal :
      ¬ G.observed.base.isTerminal history.1) :
    G.observed.base.Action history.1 :=
  Classical.choice (not_isEmpty_iff.mp hnonterminal)

/-- Realize any tagged abstract action as a legal bundle at a nonterminal
event prefix.

Matching tags use the original player action equivalence or chance action.
Mismatched tags use `fallbackAction`. -/
noncomputable def realizedAction
    (time : ℕ)
    (events : (AnalyticHistoryArena G).EventPrefix time)
    (hnonterminal :
      ¬ G.observed.base.isTerminal
        (MeasurableKernelArena.latestEventState time events).1)
    (taggedAction : CountableAction G) :
    (AnalyticHistoryArena G).ActionBundle := by
  classical
  let history :=
    MeasurableKernelArena.latestEventState time events
  exact match hmover : G.observed.base.mover history.1 with
  | some i =>
      if htag :
          taggedAction.1 =
            CountableInformation.player
              (reachablePlayerInformationAt G history i hmover
                hnonterminal) then
        ⟨history,
          G.observed.actionEquiv history i hmover
            hnonterminal
            (cast
              (congrArg CountableInformation.Action htag)
              taggedAction.2)⟩
      else
        ⟨history, fallbackAction G history hnonterminal⟩
  | none =>
      if htag :
          taggedAction.1 =
            CountableInformation.chance history
              ⟨hmover, hnonterminal⟩ then
        ⟨history,
          cast
            (congrArg CountableInformation.Action htag)
            taggedAction.2⟩
      else
        ⟨history, fallbackAction G history hnonterminal⟩

omit
  [Countable
    (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
  [Countable (CompleteHistoryAction G)] in
@[simp]
theorem realizedAction_fst
    (time : ℕ)
    (events : (AnalyticHistoryArena G).EventPrefix time)
    (hnonterminal :
      ¬ G.observed.base.isTerminal
        (MeasurableKernelArena.latestEventState time events).1)
    (taggedAction : CountableAction G) :
    (realizedAction G time events hnonterminal taggedAction).1 =
      MeasurableKernelArena.latestEventState time events := by
  unfold realizedAction
  dsimp
  split <;> split <;> rfl

omit
  [Countable
    (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
  [Countable (CompleteHistoryAction G)] in
/-- A matching player tag is realized by the original history-local
`actionEquiv`. -/
theorem realizedAction_player
    (time : ℕ)
    (events : (AnalyticHistoryArena G).EventPrefix time)
    (hnonterminal :
      ¬ G.observed.base.isTerminal
        (MeasurableKernelArena.latestEventState time events).1)
    (i : N)
    (hmover :
      G.observed.base.mover
          (MeasurableKernelArena.latestEventState time events).1 =
        some i)
    (action :
      G.observed.InfoAction i
        (G.observed.infoAt
          (MeasurableKernelArena.latestEventState time events)
          i hmover hnonterminal)) :
    realizedAction G time events hnonterminal
        (playerAction G
          (reachablePlayerInformationAt G
            (MeasurableKernelArena.latestEventState time events)
            i hmover hnonterminal)
          action) =
      ⟨MeasurableKernelArena.latestEventState time events,
        G.observed.actionEquiv
          (MeasurableKernelArena.latestEventState time events)
          i hmover hnonterminal action⟩ := by
  classical
  unfold realizedAction
  dsimp
  split
  · rename_i j hj
    have hji : j = i :=
      Option.some.inj (hj.symm.trans hmover)
    subst j
    have hproof : hj = hmover := Subsingleton.elim _ _
    cases hproof
    unfold playerAction
    dsimp only
    split
    · rename_i htag
      have htagProof : htag = rfl := Subsingleton.elim _ _
      cases htagProof
      rfl
    · rename_i htag
      exact (htag rfl).elim
  · rename_i hnone
    rw [hmover] at hnone
    contradiction

omit
  [Countable
    (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
  [Countable (CompleteHistoryAction G)] in
/-- A matching chance tag is realized by the identical local chance action. -/
theorem realizedAction_chance
    (time : ℕ)
    (events : (AnalyticHistoryArena G).EventPrefix time)
    (hnonterminal :
      ¬ G.observed.base.isTerminal
        (MeasurableKernelArena.latestEventState time events).1)
    (hmover :
      G.observed.base.mover
          (MeasurableKernelArena.latestEventState time events).1 =
        none)
    (action :
      G.observed.base.Action
        (MeasurableKernelArena.latestEventState time events).1) :
    realizedAction G time events hnonterminal
        (chanceAction G
          (MeasurableKernelArena.latestEventState time events)
          ⟨hmover, hnonterminal⟩ action) =
      ⟨MeasurableKernelArena.latestEventState time events,
        action⟩ := by
  classical
  unfold realizedAction
  dsimp
  split
  · rename_i i hi
    rw [hmover] at hi
    contradiction
  · rename_i hnone
    have hproof : hnone = hmover := Subsingleton.elim _ _
    cases hproof
    unfold chanceAction
    dsimp only
    split
    · rename_i htag
      have htagProof : htag = rfl := Subsingleton.elim _ _
      cases htagProof
      rfl
    · rename_i htag
      exact (htag rfl).elim

/-- Pointwise realization measure. It is zero at terminal prefixes and a
Dirac probability measure on a legal local bundle at nonterminal prefixes. -/
noncomputable def realizationMeasure
    (time : ℕ)
    (input :
      (AnalyticHistoryArena G).EventPrefix time ×
        CountableAction G) :
    Measure (AnalyticHistoryArena G).ActionBundle := by
  classical
  exact
    if hterminal :
        G.observed.base.isTerminal
          (MeasurableKernelArena.latestEventState time input.1).1 then
      0
    else
      @PMF.toMeasure (AnalyticHistoryArena G).ActionBundle ⊤
        (PMF.pure
          (realizedAction G time input.1 hterminal input.2))

/-- Measurable fixed realization kernel for the countable-discrete
presentation. -/
noncomputable def realizationKernel
    (time : ℕ) :
    Kernel
      ((AnalyticHistoryArena G).EventPrefix time ×
        CountableAction G)
      (AnalyticHistoryArena G).ActionBundle :=
  Kernel.ofFunOfCountable (realizationMeasure G time)

@[simp]
theorem realizationKernel_apply_terminal
    (time : ℕ)
    (events : (AnalyticHistoryArena G).EventPrefix time)
    (taggedAction : CountableAction G)
    (hterminal :
      G.observed.base.isTerminal
        (MeasurableKernelArena.latestEventState time events).1) :
    realizationKernel G time (events, taggedAction) = 0 := by
  simp [
    realizationKernel, realizationMeasure, hterminal,
    Kernel.ofFunOfCountable]

@[simp]
theorem realizationKernel_apply_nonterminal
    (time : ℕ)
    (events : (AnalyticHistoryArena G).EventPrefix time)
    (taggedAction : CountableAction G)
    (hnonterminal :
      ¬ G.observed.base.isTerminal
        (MeasurableKernelArena.latestEventState time events).1) :
    realizationKernel G time (events, taggedAction) =
      @PMF.toMeasure (AnalyticHistoryArena G).ActionBundle ⊤
        (PMF.pure
          (realizedAction G time events hnonterminal taggedAction)) := by
  simp [
    realizationKernel, realizationMeasure, hnonterminal,
    Kernel.ofFunOfCountable]

/-- Binding the realization kernel after mapping a discrete action law through
one matching canonical tag exactly pushes that law through its concrete
realization.

This helper isolates the PMF-to-measure compatibility argument shared by
player and chance branches. -/
theorem bind_mapped_realization
    {α : Type*}
    (time : ℕ)
    (events : (AnalyticHistoryArena G).EventPrefix time)
    (hnonterminal :
      ¬ G.observed.base.isTerminal
        (MeasurableKernelArena.latestEventState time events).1)
    (p : PMF α)
    (tag : α → CountableAction G)
    (concrete : α → (AnalyticHistoryArena G).ActionBundle)
    (hrealized :
      ∀ action,
        realizedAction G time events hnonterminal (tag action) =
          concrete action) :
    (@PMF.toMeasure (CountableAction G) ⊤ (p.map tag)).bind
        (fun taggedAction =>
          realizationKernel G time (events, taggedAction)) =
      @PMF.toMeasure (AnalyticHistoryArena G).ActionBundle ⊤
        (p.map concrete) := by
  simp_rw [
    realizationKernel_apply_nonterminal G time events _ hnonterminal]
  have haemeasurable :
      AEMeasurable
        (fun taggedAction : CountableAction G =>
          @PMF.toMeasure (AnalyticHistoryArena G).ActionBundle ⊤
            (PMF.pure
              (realizedAction G time events hnonterminal taggedAction)))
        (@PMF.toMeasure (CountableAction G) ⊤ (p.map tag)) :=
    (measurable_of_countable _).aemeasurable
  calc
    _ =
        @PMF.toMeasure (AnalyticHistoryArena G).ActionBundle ⊤
          ((p.map tag).bind fun taggedAction =>
            PMF.pure
              (realizedAction G time events hnonterminal taggedAction)) :=
      (PMF.toMeasure_bind_eq_bind_toMeasure
        (p.map tag)
        (fun taggedAction =>
          PMF.pure
            (realizedAction G time events hnonterminal taggedAction))
        haemeasurable).symm
    _ =
        @PMF.toMeasure (AnalyticHistoryArena G).ActionBundle ⊤
          (p.map concrete) := by
      rw [PMF.bind_map]
      have hfunction :
          ((fun taggedAction =>
              PMF.pure
                (realizedAction G time events hnonterminal taggedAction)) ∘
              tag) =
            PMF.pure ∘ concrete := by
        funext action
        simp only [Function.comp_apply]
        rw [hrealized action]
      rw [hfunction, PMF.bind_pure_comp]

theorem realizationKernel_isFinite
    (time : ℕ) :
    IsFiniteKernel (realizationKernel G time) := by
  refine ⟨⟨1, ENNReal.one_lt_top, ?_⟩⟩
  intro input
  rcases input with ⟨events, taggedAction⟩
  by_cases hterminal :
      G.observed.base.isTerminal
        (MeasurableKernelArena.latestEventState time events).1
  · rw [realizationKernel_apply_terminal G time events
      taggedAction hterminal]
    simp
  · rw [realizationKernel_apply_nonterminal G time events
      taggedAction hterminal]
    haveI :
        IsProbabilityMeasure
          (@PMF.toMeasure
            (AnalyticHistoryArena G).ActionBundle ⊤
            (PMF.pure
              (realizedAction G time events hterminal taggedAction))) :=
      inferInstance
    exact le_of_eq measure_univ

/-- Fixed canonical abstract-action realization data. -/
noncomputable def realization :
    MeasurableKernelArena.EventInformation.ActionRealization
      (eventInformation G) where
  AbstractAction := fun _time => CountableAction G
  abstractActionMeasurable := fun _time => inferInstance
  kernel := realizationKernel G
  kernel_isSFinite := by
    intro time
    letI : IsFiniteKernel (realizationKernel G time) :=
      realizationKernel_isFinite G time
    infer_instance

/-- Pointwise abstract measure selected at one canonical information tag. -/
noncomputable def abstractMeasure
    (profile : G.observed.BehavioralProfile) :
    CountableInformation G →
      Measure (CountableAction G)
  | .terminal => 0
  | .player information =>
      @PMF.toMeasure (CountableAction G) ⊤
        ((profile information.1.1 information.1.2).map
          (playerAction G information))
  | .chance history hchance =>
      @PMF.toMeasure (CountableAction G) ⊤
        ((G.chanceKernel history hchance).map
          (chanceAction G history hchance))

/-- Measurable abstract action kernel on the countable canonical information
carrier. -/
noncomputable def abstractKernel
    (profile : G.observed.BehavioralProfile) :
    Kernel (CountableInformation G) (CountableAction G) :=
  Kernel.ofFunOfCountable (abstractMeasure G profile)

omit
  [Countable (CompleteHistoryAction G)] in
@[simp]
theorem abstractKernel_terminal
    (profile : G.observed.BehavioralProfile) :
    abstractKernel G profile .terminal = 0 :=
  rfl

omit
  [Countable (CompleteHistoryAction G)] in
@[simp]
theorem abstractKernel_player
    (profile : G.observed.BehavioralProfile)
    (information : ReachablePlayerInformation G) :
    abstractKernel G profile (.player information) =
      @PMF.toMeasure (CountableAction G) ⊤
        ((profile information.1.1 information.1.2).map
          (playerAction G information)) :=
  rfl

omit
  [Countable (CompleteHistoryAction G)] in
@[simp]
theorem abstractKernel_chance
    (profile : G.observed.BehavioralProfile)
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hchance : G.observed.base.isChanceState history.1) :
    abstractKernel G profile (.chance history hchance) =
      @PMF.toMeasure (CountableAction G) ⊤
        ((G.chanceKernel history hchance).map
          (chanceAction G history hchance)) :=
  rfl

/-- At a player-controlled prefix, abstract sampling followed by canonical
realization is exactly the original concrete player-action law packaged at
the latest complete history. -/
theorem abstractKernel_bind_realization_of_mover
    (profile : G.observed.BehavioralProfile)
    (time : ℕ)
    (events : (AnalyticHistoryArena G).EventPrefix time)
    (hnonterminal :
      ¬ G.observed.base.isTerminal
        (MeasurableKernelArena.latestEventState time events).1)
    (i : N)
    (hmover :
      G.observed.base.mover
          (MeasurableKernelArena.latestEventState time events).1 =
        some i) :
    (abstractKernel G profile
        (.player
          (reachablePlayerInformationAt G
            (MeasurableKernelArena.latestEventState time events)
            i hmover hnonterminal))).bind
        (fun taggedAction =>
          realizationKernel G time (events, taggedAction)) =
      @PMF.toMeasure (AnalyticHistoryArena G).ActionBundle ⊤
        ((profile.actionLawAt G.observed
            (MeasurableKernelArena.latestEventState time events)
            i hmover hnonterminal).map
          (fun action =>
            (⟨MeasurableKernelArena.latestEventState time events,
              action⟩ :
              (AnalyticHistoryArena G).ActionBundle))) := by
  rw [abstractKernel_player]
  calc
    _ =
        @PMF.toMeasure (AnalyticHistoryArena G).ActionBundle ⊤
          ((profile i
              (G.observed.infoAt
                (MeasurableKernelArena.latestEventState time events)
                i hmover hnonterminal)).map
            (fun action =>
              (⟨MeasurableKernelArena.latestEventState time events,
                G.observed.actionEquiv
                  (MeasurableKernelArena.latestEventState time events)
                  i hmover hnonterminal action⟩ :
                (AnalyticHistoryArena G).ActionBundle))) :=
      bind_mapped_realization G time events hnonterminal
        (profile i
          (G.observed.infoAt
            (MeasurableKernelArena.latestEventState time events)
            i hmover hnonterminal))
        (playerAction G
          (reachablePlayerInformationAt G
            (MeasurableKernelArena.latestEventState time events)
            i hmover hnonterminal))
        (fun action =>
          (⟨MeasurableKernelArena.latestEventState time events,
            G.observed.actionEquiv
              (MeasurableKernelArena.latestEventState time events)
              i hmover hnonterminal action⟩ :
            (AnalyticHistoryArena G).ActionBundle))
        (realizedAction_player G time events hnonterminal i hmover)
    _ = _ := by
      unfold ObservedGame.BehavioralProfile.actionLawAt
        ObservedGame.BehavioralStrategy.actionLawAt
      congr 1
      symm
      simpa only [Function.comp_apply] using
        (PMF.map_comp
          (G.observed.actionEquiv
            (MeasurableKernelArena.latestEventState time events)
            i hmover hnonterminal)
          (profile i
            (G.observed.infoAt
              (MeasurableKernelArena.latestEventState time events)
              i hmover hnonterminal))
          (fun action =>
            (⟨MeasurableKernelArena.latestEventState time events,
              action⟩ :
              (AnalyticHistoryArena G).ActionBundle)))

/-- At a chance prefix, abstract sampling followed by canonical realization
is exactly the declared concrete chance law packaged at the latest complete
history. -/
theorem abstractKernel_bind_realization_of_chance
    (profile : G.observed.BehavioralProfile)
    (time : ℕ)
    (events : (AnalyticHistoryArena G).EventPrefix time)
    (hnonterminal :
      ¬ G.observed.base.isTerminal
        (MeasurableKernelArena.latestEventState time events).1)
    (hmover :
      G.observed.base.mover
          (MeasurableKernelArena.latestEventState time events).1 =
        none) :
    (abstractKernel G profile
        (.chance
          (MeasurableKernelArena.latestEventState time events)
          ⟨hmover, hnonterminal⟩)).bind
        (fun taggedAction =>
          realizationKernel G time (events, taggedAction)) =
      @PMF.toMeasure (AnalyticHistoryArena G).ActionBundle ⊤
        ((G.chanceKernel
            (MeasurableKernelArena.latestEventState time events)
            ⟨hmover, hnonterminal⟩).map
          (fun action =>
            (⟨MeasurableKernelArena.latestEventState time events,
              action⟩ :
              (AnalyticHistoryArena G).ActionBundle))) := by
  rw [abstractKernel_chance]
  exact
    bind_mapped_realization G time events hnonterminal
      (G.chanceKernel
        (MeasurableKernelArena.latestEventState time events)
        ⟨hmover, hnonterminal⟩)
      (chanceAction G
        (MeasurableKernelArena.latestEventState time events)
        ⟨hmover, hnonterminal⟩)
      (fun action =>
        (⟨MeasurableKernelArena.latestEventState time events,
          action⟩ :
          (AnalyticHistoryArena G).ActionBundle))
      (realizedAction_chance G time events hnonterminal hmover)

omit
  [Countable (CompleteHistoryAction G)] in
theorem abstractKernel_isFinite
    (profile : G.observed.BehavioralProfile) :
    IsFiniteKernel (abstractKernel G profile) := by
  refine ⟨⟨1, ENNReal.one_lt_top, ?_⟩⟩
  intro information
  cases information with
  | terminal =>
      rw [abstractKernel_terminal]
      simp
  | player information =>
      rw [abstractKernel_player]
      haveI :
          IsProbabilityMeasure
            (@PMF.toMeasure (CountableAction G) ⊤
              ((profile information.1.1 information.1.2).map
                (playerAction G information))) :=
        inferInstance
      exact le_of_eq measure_univ
  | chance history hchance =>
      rw [abstractKernel_chance]
      haveI :
          IsProbabilityMeasure
            (@PMF.toMeasure (CountableAction G) ⊤
              ((G.chanceKernel history hchance).map
                (chanceAction G history hchance))) :=
        inferInstance
      exact le_of_eq measure_univ

/-- Canonical realized abstract policy induced by a behavioral profile and the
declared chance kernels. -/
noncomputable def policy
    (profile : G.observed.BehavioralProfile) :
    MeasurableKernelArena.EventInformation.RealizedActionPolicy
      (realization G) where
  abstractKernel := fun _time => abstractKernel G profile
  abstractKernel_isSFinite := by
    intro _time
    change IsSFiniteKernel (abstractKernel G profile)
    letI : IsFiniteKernel (abstractKernel G profile) :=
      abstractKernel_isFinite G profile
    infer_instance
  terminal_zero := by
    intro time events hterminal
    rw [
      eventInformation_apply,
      informationAtHistory_of_terminal G
        (MeasurableKernelArena.latestEventState time events)
        hterminal]
    exact abstractKernel_terminal G profile
  nonterminal_isProbability := by
    intro time events hnonterminal
    change
      IsProbabilityMeasure
        (abstractKernel G profile
          (informationAtHistory G
            (MeasurableKernelArena.latestEventState time events)))
    cases hmover :
        G.observed.base.mover
          (MeasurableKernelArena.latestEventState time events).1 with
    | some i =>
        rw [
          informationAtHistory_of_mover G
            (MeasurableKernelArena.latestEventState time events)
            i hmover hnonterminal,
          abstractKernel_player]
        infer_instance
    | none =>
        rw [
          informationAtHistory_of_chance G
            (MeasurableKernelArena.latestEventState time events)
            hnonterminal hmover,
          abstractKernel_chance]
        infer_instance
  realization_isProbability := by
    intro time events hnonterminal
    exact Filter.Eventually.of_forall fun taggedAction => by
      change
        IsProbabilityMeasure
          (realizationKernel G time (events, taggedAction))
      rw [
        realizationKernel_apply_nonterminal G time events
          taggedAction hnonterminal]
      change
        IsProbabilityMeasure
          (@PMF.toMeasure
            (AnalyticHistoryArena G).ActionBundle ⊤
            (PMF.pure
              (realizedAction G time events hnonterminal taggedAction)))
      infer_instance
  realization_legal := by
    intro time events hnonterminal
    cases hmover :
        G.observed.base.mover
          (MeasurableKernelArena.latestEventState time events).1 with
    | some i =>
        rw [
          eventInformation_apply G time events,
          informationAtHistory_of_mover G
            (MeasurableKernelArena.latestEventState time events)
            i hmover hnonterminal]
        change
          ∀ᵐ stateAction
              ∂(abstractKernel G profile
                  (.player
                    (reachablePlayerInformationAt G
                      (MeasurableKernelArena.latestEventState time events)
                      i hmover hnonterminal))).bind
                (fun taggedAction =>
                  realizationKernel G time (events, taggedAction)),
            stateAction ∈
              (AnalyticHistoryArena G).actionFiber
                (MeasurableKernelArena.latestEventState time events)
        rw [
          abstractKernel_bind_realization_of_mover
            G profile time events hnonterminal i hmover,
          ← BehavioralProfile.toHistoryKernelPolicy_of_mover
            G profile
            (MeasurableKernelArena.latestEventState time events)
            hnonterminal i hmover]
        simpa only [
          KernelArena.Policy.toMeasurable_kernel_apply_nonterminal
            (BehavioralProfile.toHistoryKernelPolicy G profile)
            (MeasurableKernelArena.latestEventState time events)
            hnonterminal] using
          (BehavioralProfile.toHistoryKernelPolicy G profile
            ).toMeasurable.legal
              (MeasurableKernelArena.latestEventState time events)
              hnonterminal
    | none =>
        rw [
          eventInformation_apply G time events,
          informationAtHistory_of_chance G
            (MeasurableKernelArena.latestEventState time events)
            hnonterminal hmover]
        change
          ∀ᵐ stateAction
              ∂(abstractKernel G profile
                  (.chance
                    (MeasurableKernelArena.latestEventState time events)
                    ⟨hmover, hnonterminal⟩)).bind
                (fun taggedAction =>
                  realizationKernel G time (events, taggedAction)),
            stateAction ∈
              (AnalyticHistoryArena G).actionFiber
                (MeasurableKernelArena.latestEventState time events)
        rw [
          abstractKernel_bind_realization_of_chance
            G profile time events hnonterminal hmover,
          ← BehavioralProfile.toHistoryKernelPolicy_of_chance
            G profile
            (MeasurableKernelArena.latestEventState time events)
            hnonterminal hmover]
        simpa only [
          KernelArena.Policy.toMeasurable_kernel_apply_nonterminal
            (BehavioralProfile.toHistoryKernelPolicy G profile)
            (MeasurableKernelArena.latestEventState time events)
            hnonterminal] using
          (BehavioralProfile.toHistoryKernelPolicy G profile
            ).toMeasurable.legal
              (MeasurableKernelArena.latestEventState time events)
              hnonterminal

/-- The canonical realized policy compiles pointwise to the established raw
complete-history action kernel. -/
theorem compiled_kernel
    (profile : G.observed.BehavioralProfile)
    (time : ℕ)
    (events : (AnalyticHistoryArena G).EventPrefix time) :
    (policy G profile).toEventHistoryActionPolicy.kernel time events =
      (BehavioralProfile.toHistoryKernelPolicy G profile).toMeasurable.kernel
        (MeasurableKernelArena.latestEventState time events) := by
  rw [
    MeasurableKernelArena.EventInformation.RealizedActionPolicy.toEventHistoryActionPolicy_kernel_apply]
  change
    (abstractKernel G profile
      (informationAtHistory G
        (MeasurableKernelArena.latestEventState time events))).bind
        (fun taggedAction =>
          realizationKernel G time (events, taggedAction)) =
      _
  by_cases hterminal :
      G.observed.base.isTerminal
        (MeasurableKernelArena.latestEventState time events).1
  · have habstract :
        abstractKernel G profile
            (informationAtHistory G
              (MeasurableKernelArena.latestEventState time events)) =
          0 := by
      exact (policy G profile).terminal_zero time events hterminal
    rw [habstract]
    rw [Measure.bind_zero_left]
    change
      0 =
        (BehavioralProfile.toHistoryKernelPolicy G profile).toMeasurableKernel
          (MeasurableKernelArena.latestEventState time events)
    rw [
      KernelArena.Policy.toMeasurableKernel_apply_terminal
        (BehavioralProfile.toHistoryKernelPolicy G profile)
        (MeasurableKernelArena.latestEventState time events)
        hterminal]
  · cases hmover :
        G.observed.base.mover
          (MeasurableKernelArena.latestEventState time events).1 with
    | some i =>
        rw [
          informationAtHistory_of_mover G
            (MeasurableKernelArena.latestEventState time events)
            i hmover hterminal]
        rw [
          KernelArena.Policy.toMeasurable_kernel_apply_nonterminal
            (BehavioralProfile.toHistoryKernelPolicy G profile)
            (MeasurableKernelArena.latestEventState time events)
            hterminal]
        rw [
          BehavioralProfile.toHistoryKernelPolicy_of_mover
            G profile
            (MeasurableKernelArena.latestEventState time events)
            hterminal i hmover]
        exact
          abstractKernel_bind_realization_of_mover
            G profile time events hterminal i hmover
    | none =>
        rw [
          informationAtHistory_of_chance G
            (MeasurableKernelArena.latestEventState time events)
            hterminal hmover]
        rw [
          KernelArena.Policy.toMeasurable_kernel_apply_nonterminal
            (BehavioralProfile.toHistoryKernelPolicy G profile)
            (MeasurableKernelArena.latestEventState time events)
            hterminal]
        rw [
          BehavioralProfile.toHistoryKernelPolicy_of_chance
            G profile
            (MeasurableKernelArena.latestEventState time events)
            hterminal hmover]
        exact
          abstractKernel_bind_realization_of_chance
            G profile time events hterminal hmover

/-- Exact raw-policy equality of the canonical countable-discrete
presentation and the established observed-chance executor. -/
theorem compiled
    (profile : G.observed.BehavioralProfile) :
    (policy G profile).toEventHistoryActionPolicy =
      MeasurableKernelArena.HistoryActionPolicy.toEventHistoryActionPolicy
        (MeasurableKernelArena.ActionPolicy.toHistoryActionPolicy
          (BehavioralProfile.toHistoryKernelPolicy G profile).toMeasurable) := by
  apply MeasurableKernelArena.EventHistoryActionPolicy.ext
  funext time
  apply Kernel.ext
  intro events
  exact compiled_kernel G profile time events

/-- Map every original player-information point into the reachable tagged
carrier. Unreachable declared points use the terminal tag; they are never
queried by `player_informationAt`. -/
noncomputable def informationOfPlayerInformation
    (information : PlayerInformationPoint G) :
    CountableInformation G := by
  classical
  exact
    if hreachable :
        IsReachablePlayerInformation G information then
      .player ⟨information, hreachable⟩
    else
      .terminal

omit
  [Countable
    (G.observed.base.toArena.HistoryFrom G.observed.base.init)]
  [Countable (CompleteHistoryAction G)] in
/-- At an actual player-controlled history, the total original-information
map selects exactly the canonical reachable player tag. -/
@[simp]
theorem informationOfPlayerInformation_at
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (i : N)
    (hmover : G.observed.base.mover history.1 = some i)
    (hnonterminal : ¬ G.observed.base.isTerminal history.1) :
    informationOfPlayerInformation G
        ⟨i, G.observed.infoAt history i hmover hnonterminal⟩ =
      .player
        (reachablePlayerInformationAt G history i hmover
          hnonterminal) := by
  classical
  unfold informationOfPlayerInformation
  split
  · congr 1
  · rename_i hunreachable
    exact
      (hunreachable
        ⟨history, hmover, hnonterminal, rfl⟩).elim

/-- Every observed chance game satisfying the stated countability hypotheses
has a canonical discrete analytic presentation. -/
noncomputable def presentation :
    G.AnalyticPresentation where
  information := eventInformation G
  realization := realization G
  toPolicy := policy G
  compiled := compiled G
  playerInformation := fun _time playerInformation =>
    informationOfPlayerInformation G playerInformation
  player_informationAt := by
    intro time events i hmover hnonterminal
    rw [
      eventInformation_apply,
      informationAtHistory_of_mover G
        (MeasurableKernelArena.latestEventState time events)
        i hmover hnonterminal,
      informationOfPlayerInformation_at G
        (MeasurableKernelArena.latestEventState time events)
        i hmover hnonterminal]

/-- The canonical countable presentation viewed through the fully explicit
measurable-history interface. This reuses exactly the same information,
realization, and policy data. -/
noncomputable def measurablePresentation :
    G.MeasurablePresentation
      (MeasurableHistoryModel.discrete G) :=
  (presentation G).toMeasurablePresentation

/-- The canonical countable constructor as a general kernel-valued structural
presentation.  No information, realization, or executor is reimplemented. -/
noncomputable def kernelPresentation :
    G.observed.MeasurableKernelPresentation
      (MeasurableHistoryModel.discrete G) :=
  (measurablePresentation G).toKernelPresentation

/-- Embed an original PMF behavioral profile into the general kernel-valued
profile interface. -/
noncomputable def kernelBehavioralProfile
    (profile : G.observed.BehavioralProfile) :
    (kernelPresentation G).KernelBehavioralProfile :=
  (measurablePresentation G).toKernelBehavioralProfile profile

/-- The countable kernel-valued profile compiles to exactly the same raw event
policy as the prior measurable presentation. -/
theorem kernelBehavioralProfile_compiledPolicy
    (profile : G.observed.BehavioralProfile) :
    (kernelBehavioralProfile G profile).compiledPolicy =
      (measurablePresentation G).compiledPolicy profile :=
  rfl

end CountablePresentation

end ExtensiveGame.ObservedChanceGame
