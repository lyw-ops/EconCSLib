/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Behavior
import EconCSLib.GameTheory.ExtensiveGame.Observed.Refinement.Structural

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.BehaviorRefinement.Structural

Chance-aware information refinements and behavioral strategy lifting.
-/

namespace PMF

universe u

variable {α β : Type u}

/-- Casting the carrier of a PMF is pushforward through the corresponding
pointwise cast. -/
theorem cast_eq_map_cast
    (probability : PMF α) (htype : α = β) :
    cast (congrArg PMF htype) probability =
      probability.map (cast htype) := by
  subst β
  simpa using (PMF.map_id probability).symm

end PMF

namespace ExtensiveGame.ObservedChanceGame

variable {N U : Type*}

/-- Regard an observed game with no reachable chance histories as an observed
chance game. Its chance-kernel field is vacuous on complete histories from the
initial state. This adapter does not constrain unreachable ambient states. -/
def ofNoChance (G : ObservedGame N U)
    (hNoChance : G.base.NoChanceOnHistories) :
    ObservedChanceGame N U where
  observed := G
  chanceKernel := by
    intro history hchance
    have himpossible : False := by
      obtain ⟨i, hmover⟩ :=
        hNoChance history hchance.2
      exact
        (Option.some_ne_none i)
          (hmover.symm.trans hchance.1)
    exact himpossible.elim

/-- Map a chance-state proof through the strict history dynamics of an
information refinement. -/
def mapChanceStateRefinement
    {G H : ObservedGame N U}
    (r : G.InformationRefinement H)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (hchance : G.base.isChanceState history.1) :
    H.base.isChanceState
      (r.historyIso.stateEquiv history).1 := by
  constructor
  · calc
      H.base.mover
          (r.historyIso.stateEquiv history).1 =
        G.base.mover history.1 :=
          r.map_mover history
      _ = none := hchance.1
  · intro hterminal
    exact
      hchance.2
        ((r.historyIso.isTerminal_iff history).mpr hterminal)

/-- A chance-aware information refinement.

The observed layer may refine private/public information and strategic
decision states. Chance behavior itself is not refined: its normalized action
law must commute exactly with the strict history-action equivalence. -/
structure InformationRefinement
    (G H : ObservedChanceGame N U) where
  /-- Information refinement of the observed EFG structure. -/
  observedRefinement :
    G.observed.InformationRefinement H.observed
  /-- Exact naturality of every chance action law. -/
  map_chanceKernel :
    ∀ (history :
        G.observed.base.toArena.HistoryFrom
          G.observed.base.init)
      (hchance :
        G.observed.base.isChanceState history.1),
      (G.chanceKernel history hchance).map
          (observedRefinement.historyIso.actionEquiv
            history) =
        H.chanceKernel
          (observedRefinement.historyIso.stateEquiv
            history)
          (mapChanceStateRefinement
            observedRefinement history hchance)

namespace InformationRefinement

variable {G H : ObservedChanceGame N U}

/-- Chance-aware refinements are determined by their observed information
refinement; chance-kernel naturality is propositional. -/
@[ext]
theorem ext (r s : G.InformationRefinement H)
    (hObserved :
      r.observedRefinement = s.observedRefinement) :
    r = s := by
  cases r
  cases s
  cases hObserved
  rfl

/-- Identity chance-aware information refinement. -/
def refl (G : ObservedChanceGame N U) :
    G.InformationRefinement G where
  observedRefinement :=
    ObservedGame.InformationRefinement.refl
      G.observed
  map_chanceKernel := by
    intro history hchance
    simpa using
      PMF.map_id (G.chanceKernel history hchance)

/-- Compose chance-aware information refinements. -/
def trans {K : ObservedChanceGame N U}
    (r : G.InformationRefinement H)
    (s : H.InformationRefinement K) :
    G.InformationRefinement K where
  observedRefinement :=
    r.observedRefinement.trans
      s.observedRefinement
  map_chanceKernel := by
    intro history hchance
    let middleChance :=
      mapChanceStateRefinement
        r.observedRefinement history hchance
    change
      (G.chanceKernel history hchance).map
          ((fun action =>
            s.observedRefinement.historyIso.actionEquiv
              (r.observedRefinement.historyIso.stateEquiv
                history)
              action) ∘
            r.observedRefinement.historyIso.actionEquiv
              history) =
        K.chanceKernel
          (s.observedRefinement.historyIso.stateEquiv
            (r.observedRefinement.historyIso.stateEquiv
              history))
          _
    rw [← PMF.map_comp]
    rw [r.map_chanceKernel history hchance]
    exact
      s.map_chanceKernel
        (r.observedRefinement.historyIso.stateEquiv
          history)
        middleChance

/-- Identity is a left unit for chance-aware refinement composition. -/
@[simp]
theorem refl_trans (r : G.InformationRefinement H) :
    (refl G).trans r = r := by
  apply InformationRefinement.ext
  exact ObservedGame.InformationRefinement.refl_trans
    r.observedRefinement

/-- Identity is a right unit for chance-aware refinement composition. -/
@[simp]
theorem trans_refl (r : G.InformationRefinement H) :
    r.trans (refl H) = r := by
  apply InformationRefinement.ext
  exact ObservedGame.InformationRefinement.trans_refl
    r.observedRefinement

/-- Composition of chance-aware information refinements is associative. -/
theorem trans_assoc {K L : ObservedChanceGame N U}
    (r : G.InformationRefinement H)
    (s : H.InformationRefinement K)
    (t : K.InformationRefinement L) :
    (r.trans s).trans t = r.trans (s.trans t) := by
  apply InformationRefinement.ext
  exact ObservedGame.InformationRefinement.trans_assoc
    r.observedRefinement
    s.observedRefinement
    t.observedRefinement

end InformationRefinement

end ExtensiveGame.ObservedChanceGame

namespace ExtensiveGame.ObservedGame.InformationRefinement

variable {N U : Type*}
variable {G H : ObservedGame N U}

/-- Dependent function evaluation commutes with transport of its index. -/
private theorem dependent_apply_eq_cast
    {α : Type*} {fiber : α → Type*}
    (function : (index : α) → fiber index)
    {source target : α}
    (hindex : source = target) :
    function target =
      cast (congrArg fiber hindex)
        (function source) := by
  subst target
  rfl

/-- Lift a coarse behavioral strategy to the finer information structure by
exact PMF pushforward at every fine information state. -/
noncomputable def mapBehavioralStrategy
    (r : G.InformationRefinement H) (i : N)
    (strategy : G.BehavioralStrategy i) :
    H.BehavioralStrategy i :=
  fun information =>
    (strategy (r.forgetInfo i information)).map
      (r.infoActionEquiv i information)

/-- Lift a complete coarse behavioral profile player by player. -/
noncomputable def mapBehavioralProfile
    (r : G.InformationRefinement H)
    (profile : G.BehavioralProfile) :
    H.BehavioralProfile :=
  fun i => r.mapBehavioralStrategy i (profile i)

/-- Identity refinements leave behavioral strategies unchanged. -/
@[simp]
theorem refl_mapBehavioralStrategy
    (i : N) (strategy : G.BehavioralStrategy i) :
    (ObservedGame.InformationRefinement.refl G).mapBehavioralStrategy
        i strategy =
      strategy := by
  funext information
  change
    (strategy information).map (Equiv.refl _) =
      strategy information
  simpa using PMF.map_id (strategy information)

/-- Identity refinements leave behavioral profiles unchanged. -/
@[simp]
theorem refl_mapBehavioralProfile
    (profile : G.BehavioralProfile) :
    (ObservedGame.InformationRefinement.refl G).mapBehavioralProfile
        profile =
      profile := by
  funext i
  exact refl_mapBehavioralStrategy i (profile i)

/-- Behavioral strategy lifting along a composite information refinement is
successive PMF pushforward. -/
@[simp]
theorem trans_mapBehavioralStrategy
    {K : ObservedGame N U}
    (r : G.InformationRefinement H)
    (s : H.InformationRefinement K)
    (i : N)
    (strategy : G.BehavioralStrategy i) :
    (r.trans s).mapBehavioralStrategy i strategy =
      s.mapBehavioralStrategy i
        (r.mapBehavioralStrategy i strategy) := by
  funext information
  unfold mapBehavioralStrategy
  rw [PMF.map_comp]
  rfl

/-- Behavioral profile lifting along a composite refinement is successive
lifting. -/
@[simp]
theorem trans_mapBehavioralProfile
    {K : ObservedGame N U}
    (r : G.InformationRefinement H)
    (s : H.InformationRefinement K)
    (profile : G.BehavioralProfile) :
    (r.trans s).mapBehavioralProfile profile =
      s.mapBehavioralProfile
        (r.mapBehavioralProfile profile) := by
  funext i
  exact
    r.trans_mapBehavioralStrategy s i (profile i)

@[simp]
theorem mapBehavioralProfile_apply
    (r : G.InformationRefinement H)
    (profile : G.BehavioralProfile) (i : N) :
    r.mapBehavioralProfile profile i =
      r.mapBehavioralStrategy i (profile i) :=
  rfl

/-- Every fine behavioral strategy is represented by a lifted coarse
behavioral strategy. This is the exact deviation-lifting hypothesis for
two-way behavioral equilibrium transfer. -/
def BehavioralStrategySurjective
    (r : G.InformationRefinement H) : Prop :=
  ∀ i : N,
    Function.Surjective
      (r.mapBehavioralStrategy i)

/-- Behavioral-profile lifting commutes with unilateral deviation. -/
theorem mapBehavioralProfile_deviate
    [DecidableEq N]
    (r : G.InformationRefinement H)
    (profile : G.BehavioralProfile)
    (i : N)
    (strategy : G.BehavioralStrategy i) :
    r.mapBehavioralProfile
        (profile.deviate G i strategy) =
      (r.mapBehavioralProfile profile).deviate
        H i (r.mapBehavioralStrategy i strategy) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [ObservedGame.BehavioralProfile.deviate,
      mapBehavioralProfile]
  · simp [ObservedGame.BehavioralProfile.deviate,
      mapBehavioralProfile, hji]

/-- A lifted behavioral profile's abstract action law at a corresponding fine
history is the source law pushed through `infoActionEquivAt`. -/
theorem mapBehavioralProfile_infoAt
    (r : G.InformationRefinement H)
    (profile : G.BehavioralProfile)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hsource : G.base.mover history.1 = some i)
    (htarget :
      H.base.mover
          (r.historyIso.stateEquiv history).1 =
        some i) :
    r.mapBehavioralProfile profile i
        (H.infoAt
          (r.historyIso.stateEquiv history)
          i htarget) =
      (profile i
        (G.infoAt history i hsource)).map
          (r.infoActionEquivAt
            history i hsource htarget) := by
  let sourceInformation :=
    G.infoAt history i hsource
  let targetInformation :=
    H.infoAt
      (r.historyIso.stateEquiv history) i htarget
  have hinfo :
      sourceInformation =
        r.forgetInfo i targetInformation :=
    r.map_infoAt history i hsource htarget
  have hprobability :
      profile i (r.forgetInfo i targetInformation) =
        cast
          (congrArg
            (fun information =>
              PMF (G.InfoAction i information))
            hinfo)
          (profile i sourceInformation) := by
    exact
      dependent_apply_eq_cast
        (profile i) hinfo
  change
    (profile i
        (r.forgetInfo i targetInformation)).map
        (r.infoActionEquiv i targetInformation) =
      (profile i sourceInformation).map
        (r.infoActionEquivAt
          history i hsource htarget)
  rw [hprobability,
    PMF.cast_eq_map_cast]
  rw [PMF.map_comp]
  rfl

/-- At corresponding player histories, the concrete behavioral action law is
the exact pushforward of the coarse law through the strict history-action
equivalence. -/
theorem map_behavioralActionLaw
    (r : G.InformationRefinement H)
    (profile : G.BehavioralProfile)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hsource : G.base.mover history.1 = some i)
    (htarget :
      H.base.mover
          (r.historyIso.stateEquiv history).1 =
        some i) :
    (profile.actionLawAt G history i hsource).map
        (r.historyIso.actionEquiv history) =
      (r.mapBehavioralProfile profile).actionLawAt H
        (r.historyIso.stateEquiv history)
        i htarget := by
  unfold
    ObservedGame.BehavioralProfile.actionLawAt
    ObservedGame.BehavioralStrategy.actionLawAt
  rw [r.mapBehavioralProfile_infoAt
    profile history i hsource htarget]
  let probability :=
    profile i (G.infoAt history i hsource)
  calc
    (probability.map
        (G.actionEquiv history i hsource)).map
          (r.historyIso.actionEquiv history) =
      probability.map
        ((r.historyIso.actionEquiv history) ∘
          (G.actionEquiv history i hsource)) :=
            PMF.map_comp
              (G.actionEquiv history i hsource)
              probability
              (r.historyIso.actionEquiv history)
    _ = probability.map
        ((H.actionEquiv
            (r.historyIso.stateEquiv history)
            i htarget) ∘
          (r.infoActionEquivAt
            history i hsource htarget)) := by
          apply congrArg
            (fun actionMap =>
              probability.map actionMap)
          funext action
          exact
            (r.map_infoActionEquivAt
              history i hsource htarget action).symm
    _ = (probability.map
          (r.infoActionEquivAt
            history i hsource htarget)).map
        (H.actionEquiv
          (r.historyIso.stateEquiv history)
          i htarget) :=
      (PMF.map_comp
        (r.infoActionEquivAt
          history i hsource htarget)
        probability
        (H.actionEquiv
          (r.historyIso.stateEquiv history)
          i htarget)).symm

end ExtensiveGame.ObservedGame.InformationRefinement
