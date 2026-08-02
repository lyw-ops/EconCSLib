/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.DependentFiber
import EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled

/-!
# Payoff-free observed-game morphism core

This leaf owns the structural comparison of `ControlledObservedGame`.
`ControlledObservedGame.Hom` records a directional map of histories and
information carriers. `ControlledObservedGame.Iso` is the strict invertible
relation: one source step is one target step, dependent action fibers are
equivalent, and concrete realization commutes.

Continuation roots are not fields of either relation. Their one-way or exact
correspondence is supplied independently through
`MapsRootPresentations`/`PreservesRootPresentations`.

Payoff compatibility and conversion from the legacy `ObservedGame.Iso` live
in `ControlledMorphismCompat`. Lawful-subgame and recall transport live in
their respective `ControlledMorphism` leaves, so this structural core has no
subgame, recall, finite-EFG, structural-length, or payoff-aware observed-game
dependency.
-/

namespace ExtensiveGame.ControlledObservedGame

variable {N : Type*}

/-! ## Directional structural homomorphisms -/

/-- A directional map of payoff-free histories, observations, and information
carriers.

This relation intentionally does not claim execution-law preservation:
dependent information actions are mapped as carriers, while exact commuting
with concrete action realization is reserved for `Iso` and stronger
simulation certificates. -/
structure Hom (G H : ControlledObservedGame N) where
  /-- Strict one-step map of complete-history arenas. -/
  historyHom : G.base.unfold.toArena.Hom H.base.unfold.toArena
  /-- The empty history is preserved. -/
  map_init :
    historyHom.state
        (Arena.HistoryFrom.nil G.base.toArena G.base.init) =
      Arena.HistoryFrom.nil H.base.toArena H.base.init
  /-- Mover labels are preserved. -/
  map_mover :
    ∀ history : G.base.History,
      H.base.mover (historyHom.state history).1 =
        G.base.mover history.1
  /-- Map private observations. -/
  mapObservation : (i : N) → G.Observation i → H.Observation i
  /-- Private observation commutes with history mapping. -/
  map_observe :
    ∀ (i : N) (history : G.base.History),
      mapObservation i (G.observe i history) =
        H.observe i (historyHom.state history)
  /-- Map public observations. -/
  mapPublic : G.PublicObservation → H.PublicObservation
  /-- Public observation commutes with history mapping. -/
  map_publicObserve :
    ∀ history : G.base.History,
      mapPublic (G.publicObserve history) =
        H.publicObserve (historyHom.state history)
  /-- Map decision information. -/
  mapInfo : (i : N) → G.InfoState i → H.InfoState i
  /-- Decision information commutes at represented histories. -/
  map_infoAt :
    ∀ (history : G.base.History) (i : N)
      (hsource : G.base.mover history.1 = some i)
      (htarget :
        H.base.mover (historyHom.state history).1 = some i),
      mapInfo i (G.infoAt history i hsource) =
        H.infoAt (historyHom.state history) i htarget
  /-- Map dependent information-action carriers. -/
  mapInfoAction :
    ∀ (i : N) (information : G.InfoState i),
      G.InfoAction i information →
        H.InfoAction i (mapInfo i information)

namespace Hom

variable {G H : ControlledObservedGame N}

/-- A structural hom maps selected source roots into selected target roots. -/
def MapsRootPresentations
    (f : G.Hom H)
    (sourceRoots : G.ContinuationRootPresentation)
    (targetRoots : H.ContinuationRootPresentation) : Prop :=
  ∀ history : G.base.History,
    sourceRoots.IsRoot history →
      targetRoots.IsRoot (f.historyHom.state history)

/-- Identity structural homomorphism. -/
def refl (G : ControlledObservedGame N) : G.Hom G where
  historyHom := Arena.Hom.id G.base.unfold.toArena
  map_init := rfl
  map_mover := by intro history; rfl
  mapObservation := fun _ observation => observation
  map_observe := by intro i history; rfl
  mapPublic := id
  map_publicObserve := by intro history; rfl
  mapInfo := fun _ information => information
  map_infoAt := by
    intro history i hsource htarget
    congr
  mapInfoAction := fun _ _ action => action

/-- Composition of directional structural homomorphisms. -/
def trans {K : ControlledObservedGame N}
    (f : G.Hom H) (g : H.Hom K) : G.Hom K where
  historyHom := g.historyHom.comp f.historyHom
  map_init := by
    change
      g.historyHom.state
          (f.historyHom.state
            (Arena.HistoryFrom.nil
              G.base.toArena G.base.init)) =
        Arena.HistoryFrom.nil K.base.toArena K.base.init
    rw [f.map_init, g.map_init]
  map_mover := by
    intro history
    change
      K.base.mover
          (g.historyHom.state
            (f.historyHom.state history)).1 =
        G.base.mover history.1
    rw [g.map_mover, f.map_mover]
  mapObservation := fun i =>
    g.mapObservation i ∘ f.mapObservation i
  map_observe := by
    intro i history
    change
      g.mapObservation i
          (f.mapObservation i (G.observe i history)) =
        K.observe i
          (g.historyHom.state
            (f.historyHom.state history))
    rw [f.map_observe, g.map_observe]
  mapPublic := g.mapPublic ∘ f.mapPublic
  map_publicObserve := by
    intro history
    change
      g.mapPublic (f.mapPublic (G.publicObserve history)) =
        K.publicObserve
          (g.historyHom.state
            (f.historyHom.state history))
    rw [f.map_publicObserve, g.map_publicObserve]
  mapInfo := fun i => g.mapInfo i ∘ f.mapInfo i
  map_infoAt := by
    intro history i hsource htarget
    have hmiddle :
        H.base.mover (f.historyHom.state history).1 = some i := by
      rw [f.map_mover history]
      exact hsource
    exact
      (congrArg (g.mapInfo i)
        (f.map_infoAt history i hsource hmiddle)).trans
        (g.map_infoAt
          (f.historyHom.state history) i hmiddle htarget)
  mapInfoAction := fun i information action =>
    g.mapInfoAction i (f.mapInfo i information)
      (f.mapInfoAction i information action)

/-- Structural hom composition preserves one-way root mapping. -/
theorem trans_mapsRootPresentations
    {K : ControlledObservedGame N}
    (f : G.Hom H) (g : H.Hom K)
    {sourceRoots : G.ContinuationRootPresentation}
    {middleRoots : H.ContinuationRootPresentation}
    {targetRoots : K.ContinuationRootPresentation}
    (hf : f.MapsRootPresentations sourceRoots middleRoots)
    (hg : g.MapsRootPresentations middleRoots targetRoots) :
    (f.trans g).MapsRootPresentations sourceRoots targetRoots := by
  intro history hroot
  exact hg _ (hf history hroot)

end Hom

/-! ## Directional information refinement -/

/-- A payoff-free information refinement from a coarse presentation `G` to a
finer presentation `H`.

The complete-history dynamics are strictly isomorphic. Fine private, public,
and decision information forgets to coarse information, while every coarse
information action lifts to the corresponding fine fiber. -/
structure InformationRefinement
    (G H : ControlledObservedGame N) where
  /-- Strict equivalence of complete-history dynamics. -/
  historyIso : G.base.unfold.toArena.Iso H.base.unfold.toArena
  /-- Empty histories correspond. -/
  map_init :
    historyIso.stateEquiv
        (Arena.HistoryFrom.nil G.base.toArena G.base.init) =
      Arena.HistoryFrom.nil H.base.toArena H.base.init
  /-- Mover labels correspond. -/
  map_mover :
    ∀ history : G.base.History,
      H.base.mover (historyIso.stateEquiv history).1 =
        G.base.mover history.1
  /-- Forget fine private observations. -/
  forgetObservation :
    (i : N) → H.Observation i → G.Observation i
  /-- Private-observation forgetting commutes with history transport. -/
  forget_observe :
    ∀ (i : N) (history : G.base.History),
      forgetObservation i
          (H.observe i (historyIso.stateEquiv history)) =
        G.observe i history
  /-- Forget fine public observations. -/
  forgetPublic : H.PublicObservation → G.PublicObservation
  /-- Public-observation forgetting commutes with history transport. -/
  forget_publicObserve :
    ∀ history : G.base.History,
      forgetPublic
          (H.publicObserve (historyIso.stateEquiv history)) =
        G.publicObserve history
  /-- Private-to-public projection commutes with forgetting. -/
  forget_publicOf :
    ∀ (i : N) (observation : H.Observation i),
      forgetPublic (H.publicOf i observation) =
        G.publicOf i (forgetObservation i observation)
  /-- Forget fine decision information. -/
  forgetInfo :
    (i : N) → H.InfoState i → G.InfoState i
  /-- Information-to-observation projection commutes with forgetting. -/
  forget_infoObserve :
    ∀ (i : N) (information : H.InfoState i),
      forgetObservation i (H.infoObserve i information) =
        G.infoObserve i (forgetInfo i information)
  /-- Lift coarse information actions to each fine information fiber. -/
  infoActionEquiv :
    ∀ (i : N) (information : H.InfoState i),
      G.InfoAction i (forgetInfo i information) ≃
        H.InfoAction i information
  /-- Forgetting represented fine information recovers source information. -/
  map_infoAt :
    ∀ (history : G.base.History) (i : N)
      (hsource : G.base.mover history.1 = some i)
      (htarget :
        H.base.mover (historyIso.stateEquiv history).1 = some i),
      G.infoAt history i hsource =
        forgetInfo i
          (H.infoAt (historyIso.stateEquiv history) i htarget)
  /-- Lifting and realizing a coarse action commutes with strict concrete
  history-action transport. -/
  map_infoActionAt :
    ∀ (history : G.base.History) (i : N)
      (hsource : G.base.mover history.1 = some i)
      (htarget :
        H.base.mover (historyIso.stateEquiv history).1 = some i)
      (action : G.InfoAction i (G.infoAt history i hsource)),
      H.actionEquiv (historyIso.stateEquiv history) i htarget
          (infoActionEquiv i
            (H.infoAt
              (historyIso.stateEquiv history) i htarget)
            (cast
              (congrArg (G.InfoAction i)
                (map_infoAt history i hsource htarget))
              action)) =
        historyIso.actionEquiv history
          (G.actionEquiv history i hsource action)

namespace InformationRefinement

variable {G H : ControlledObservedGame N}

/-- A refinement maps selected coarse roots into selected fine roots. -/
def MapsRootPresentations
    (r : G.InformationRefinement H)
    (sourceRoots : G.ContinuationRootPresentation)
    (targetRoots : H.ContinuationRootPresentation) : Prop :=
  ∀ history : G.base.History,
    sourceRoots.IsRoot history →
      targetRoots.IsRoot (r.historyIso.stateEquiv history)

/-- Exact external root correspondence along an information refinement. -/
def PreservesRootPresentations
    (r : G.InformationRefinement H)
    (sourceRoots : G.ContinuationRootPresentation)
    (targetRoots : H.ContinuationRootPresentation) : Prop :=
  ∀ history : G.base.History,
    sourceRoots.IsRoot history ↔
      targetRoots.IsRoot (r.historyIso.stateEquiv history)

/-- Lift a coarse payoff-free pure strategy to the finer information
presentation. -/
def mapStrategy
    (r : G.InformationRefinement H) (i : N)
    (strategy : G.PureStrategy i) :
    H.PureStrategy i :=
  fun information =>
    r.infoActionEquiv i information
      (strategy (r.forgetInfo i information))

/-- Lift a payoff-free pure profile componentwise. -/
def mapProfile
    (r : G.InformationRefinement H)
    (profile : G.PureProfile) :
    H.PureProfile :=
  fun i => r.mapStrategy i (profile i)

/-- Coverage of all target strategies is an additional hypothesis, not part
of a genuine information refinement. -/
def StrategySurjective
    (r : G.InformationRefinement H) : Prop :=
  ∀ i : N, Function.Surjective (r.mapStrategy i)

/-- Refinement strategy lifting commutes with unilateral update. -/
theorem mapProfile_update [DecidableEq N]
    (r : G.InformationRefinement H)
    (profile : G.PureProfile)
    (who : N) (deviation : G.PureStrategy who) :
    r.mapProfile (Function.update profile who deviation) =
      Function.update (r.mapProfile profile) who
        (r.mapStrategy who deviation) := by
  funext i
  by_cases hi : i = who
  · subst i
    simp [mapProfile]
  · simp [mapProfile, hi]

/-- Identity payoff-free information refinement. -/
def refl (G : ControlledObservedGame N) :
    G.InformationRefinement G where
  historyIso := Arena.Iso.refl G.base.unfold.toArena
  map_init := rfl
  map_mover := by intro history; rfl
  forgetObservation := fun _ observation => observation
  forget_observe := by intro i history; rfl
  forgetPublic := id
  forget_publicObserve := by intro history; rfl
  forget_publicOf := by intro i observation; rfl
  forgetInfo := fun _ information => information
  forget_infoObserve := by intro i information; rfl
  infoActionEquiv := fun _ _ => Equiv.refl _
  map_infoAt := by
    intro history i hsource htarget
    congr
  map_infoActionAt := by
    intro history i hsource htarget action
    rfl

end InformationRefinement

/-! ## Strict structural isomorphisms -/

/-- A strict payoff-free observed-game isomorphism.

Besides equivalences of all carriers, the final square states that mapping an
abstract information action and then realizing it is exactly the strict
history-action map. No payoff compatibility is present. -/
