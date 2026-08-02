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
