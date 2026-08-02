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
structure Iso (G H : ControlledObservedGame N) where
  /-- Strict isomorphism of complete-history arenas. -/
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
  /-- Equivalence of private-observation carriers. -/
  observationEquiv :
    (i : N) → G.Observation i ≃ H.Observation i
  /-- Private observation commutes. -/
  map_observe :
    ∀ (i : N) (history : G.base.History),
      observationEquiv i (G.observe i history) =
        H.observe i (historyIso.stateEquiv history)
  /-- Equivalence of public-observation carriers. -/
  publicEquiv : G.PublicObservation ≃ H.PublicObservation
  /-- Public observation commutes. -/
  map_publicObserve :
    ∀ history : G.base.History,
      publicEquiv (G.publicObserve history) =
        H.publicObserve (historyIso.stateEquiv history)
  /-- Private-to-public projection commutes. -/
  map_publicOf :
    ∀ (i : N) (observation : G.Observation i),
      publicEquiv (G.publicOf i observation) =
        H.publicOf i (observationEquiv i observation)
  /-- Equivalence of decision-information carriers. -/
  infoStateEquiv :
    (i : N) → G.InfoState i ≃ H.InfoState i
  /-- Information-to-observation projection commutes. -/
  map_infoObserve :
    ∀ (i : N) (information : G.InfoState i),
      observationEquiv i (G.infoObserve i information) =
        H.infoObserve i (infoStateEquiv i information)
  /-- Equivalence of dependent information-action fibers. -/
  infoActionEquiv :
    ∀ (i : N) (information : G.InfoState i),
      G.InfoAction i information ≃
        H.InfoAction i (infoStateEquiv i information)
  /-- Represented decision information commutes. -/
  map_infoAt :
    ∀ (history : G.base.History) (i : N)
      (hsource : G.base.mover history.1 = some i)
      (htarget :
        H.base.mover (historyIso.stateEquiv history).1 = some i),
      infoStateEquiv i (G.infoAt history i hsource) =
        H.infoAt (historyIso.stateEquiv history) i htarget
  /-- Abstract-action realization commutes with the history action map. -/
  map_infoActionAt :
    ∀ (history : G.base.History) (i : N)
      (hsource : G.base.mover history.1 = some i)
      (htarget :
        H.base.mover (historyIso.stateEquiv history).1 = some i)
      (action : G.InfoAction i (G.infoAt history i hsource)),
      H.actionEquiv (historyIso.stateEquiv history) i htarget
          (cast
            (congrArg (H.InfoAction i)
              (map_infoAt history i hsource htarget))
            (infoActionEquiv i
              (G.infoAt history i hsource) action)) =
        historyIso.actionEquiv history
          (G.actionEquiv history i hsource action)

namespace Iso

variable {G H : ControlledObservedGame N}

/-- Strict isomorphisms are determined by their carrier equivalences. -/
@[ext]
theorem ext (e f : G.Iso H)
    (hhistory : e.historyIso = f.historyIso)
    (hobservation : e.observationEquiv = f.observationEquiv)
    (hpublic : e.publicEquiv = f.publicEquiv)
    (hinfoState : e.infoStateEquiv = f.infoStateEquiv)
    (hinfoAction : HEq e.infoActionEquiv f.infoActionEquiv) :
    e = f := by
  cases e
  cases f
  cases hhistory
  cases hobservation
  cases hpublic
  cases hinfoState
  cases hinfoAction
  rfl

/-- Exact correspondence of external root presentations. -/
def PreservesRootPresentations
    (e : G.Iso H)
    (sourceRoots : G.ContinuationRootPresentation)
    (targetRoots : H.ContinuationRootPresentation) : Prop :=
  ∀ history : G.base.History,
    sourceRoots.IsRoot history ↔
      targetRoots.IsRoot (e.historyIso.stateEquiv history)

/-- Forget invertibility while retaining the directional carrier map. -/
def toHom (e : G.Iso H) : G.Hom H where
  historyHom := e.historyIso.toHom
  map_init := e.map_init
  map_mover := e.map_mover
  mapObservation := fun i => e.observationEquiv i
  map_observe := e.map_observe
  mapPublic := e.publicEquiv
  map_publicObserve := e.map_publicObserve
  mapInfo := fun i => e.infoStateEquiv i
  map_infoAt := e.map_infoAt
  mapInfoAction := fun i information =>
    e.infoActionEquiv i information

/-- Exact root correspondence implies directional root mapping. -/
theorem mapsRootPresentations
    (e : G.Iso H)
    {sourceRoots : G.ContinuationRootPresentation}
    {targetRoots : H.ContinuationRootPresentation}
    (hroots :
      e.PreservesRootPresentations sourceRoots targetRoots) :
    e.toHom.MapsRootPresentations sourceRoots targetRoots :=
  fun history hroot => (hroots history).mp hroot

/-- The pure-strategy equivalence induced by information fibers. -/
def strategyEquiv (e : G.Iso H) (i : N) :
    G.PureStrategy i ≃ H.PureStrategy i :=
  (e.infoStateEquiv i).piCongr
    (e.infoActionEquiv i)

/-- Cast-stable information-action equivalence at corresponding decision
histories. -/
def infoActionEquivAt
    (e : G.Iso H)
    (history : G.base.History)
    (i : N)
    (hsource : G.base.mover history.1 = some i)
    (htarget :
      H.base.mover (e.historyIso.stateEquiv history).1 = some i) :
    G.InfoAction i (G.infoAt history i hsource) ≃
      H.InfoAction i
        (H.infoAt (e.historyIso.stateEquiv history) i htarget) :=
  Equiv.fiberEquivAt
    (e.infoStateEquiv i)
    (e.infoActionEquiv i)
    (G.infoAt history i hsource)
    (H.infoAt (e.historyIso.stateEquiv history) i htarget)
    (e.map_infoAt history i hsource htarget)

@[simp]
theorem infoActionEquivAt_apply
    (e : G.Iso H)
    (history : G.base.History)
    (i : N)
    (hsource : G.base.mover history.1 = some i)
    (htarget :
      H.base.mover (e.historyIso.stateEquiv history).1 = some i)
    (action : G.InfoAction i (G.infoAt history i hsource)) :
    e.infoActionEquivAt history i hsource htarget action =
      cast
        (congrArg (H.InfoAction i)
          (e.map_infoAt history i hsource htarget))
        (e.infoActionEquiv i
          (G.infoAt history i hsource) action) :=
  rfl

/-- Realization of the local information-action equivalence commutes with
the strict concrete history-action equivalence. -/
theorem map_infoActionEquivAt
    (e : G.Iso H)
    (history : G.base.History)
    (i : N)
    (hsource : G.base.mover history.1 = some i)
    (htarget :
      H.base.mover (e.historyIso.stateEquiv history).1 = some i)
    (action : G.InfoAction i (G.infoAt history i hsource)) :
    H.actionEquiv
        (e.historyIso.stateEquiv history) i htarget
        (e.infoActionEquivAt
          history i hsource htarget action) =
      e.historyIso.actionEquiv history
        (G.actionEquiv history i hsource action) :=
  e.map_infoActionAt history i hsource htarget action

/-- Map a complete payoff-free pure profile. -/
def mapProfile (e : G.Iso H)
    (profile : G.PureProfile) : H.PureProfile :=
  fun i => e.strategyEquiv i (profile i)

/-- Mapping a unilateral update commutes with strict profile transport. -/
theorem mapProfile_update [DecidableEq N]
    (e : G.Iso H)
    (profile : G.PureProfile)
    (who : N) (deviation : G.PureStrategy who) :
    e.mapProfile (Function.update profile who deviation) =
      Function.update (e.mapProfile profile) who
        (e.strategyEquiv who deviation) := by
  funext i
  by_cases hi : i = who
  · subst i
    simp [mapProfile]
  · simp [mapProfile, hi]

/-- Identity strict payoff-free isomorphism. -/
def refl (G : ControlledObservedGame N) : G.Iso G where
  historyIso := Arena.Iso.refl G.base.unfold.toArena
  map_init := rfl
  map_mover := by intro history; rfl
  observationEquiv := fun _ => Equiv.refl _
  map_observe := by intro i history; rfl
  publicEquiv := Equiv.refl _
  map_publicObserve := by intro history; rfl
  map_publicOf := by intro i observation; rfl
  infoStateEquiv := fun _ => Equiv.refl _
  map_infoObserve := by intro i information; rfl
  infoActionEquiv := fun _ _ => Equiv.refl _
  map_infoAt := by
    intro history i hsource htarget
    congr
  map_infoActionAt := by
    intro history i hsource htarget action
    rfl

/-- The information equality used by strict-isomorphism composition. -/
def transInfoAt {K : ControlledObservedGame N}
    (e : G.Iso H) (f : H.Iso K)
    (history : G.base.History) (i : N)
    (hsource : G.base.mover history.1 = some i)
    (hmiddle :
      H.base.mover (e.historyIso.stateEquiv history).1 = some i)
    (htarget :
      K.base.mover
        (f.historyIso.stateEquiv
          (e.historyIso.stateEquiv history)).1 = some i) :
    (e.infoStateEquiv i).trans (f.infoStateEquiv i)
        (G.infoAt history i hsource) =
      K.infoAt
        (f.historyIso.stateEquiv
          (e.historyIso.stateEquiv history)) i htarget :=
  (congrArg (f.infoStateEquiv i)
    (e.map_infoAt history i hsource hmiddle)).trans
      (f.map_infoAt
        (e.historyIso.stateEquiv history)
        i hmiddle htarget)

/-- Compose strict payoff-free observed-game isomorphisms. -/
def trans {K : ControlledObservedGame N}
    (e : G.Iso H) (f : H.Iso K) : G.Iso K where
  historyIso := e.historyIso.trans f.historyIso
  map_init := by
    change
      f.historyIso.stateEquiv
          (e.historyIso.stateEquiv
            (Arena.HistoryFrom.nil
              G.base.toArena G.base.init)) =
        Arena.HistoryFrom.nil K.base.toArena K.base.init
    rw [e.map_init, f.map_init]
  map_mover := by
    intro history
    change
      K.base.mover
          (f.historyIso.stateEquiv
            (e.historyIso.stateEquiv history)).1 =
        G.base.mover history.1
    rw [f.map_mover, e.map_mover]
  observationEquiv := fun i =>
    (e.observationEquiv i).trans (f.observationEquiv i)
  map_observe := by
    intro i history
    change
      f.observationEquiv i
          (e.observationEquiv i (G.observe i history)) =
        K.observe i
          (f.historyIso.stateEquiv
            (e.historyIso.stateEquiv history))
    rw [e.map_observe, f.map_observe]
  publicEquiv := e.publicEquiv.trans f.publicEquiv
  map_publicObserve := by
    intro history
    change
      f.publicEquiv (e.publicEquiv (G.publicObserve history)) =
        K.publicObserve
          (f.historyIso.stateEquiv
            (e.historyIso.stateEquiv history))
    rw [e.map_publicObserve, f.map_publicObserve]
  map_publicOf := by
    intro i observation
    change
      f.publicEquiv
          (e.publicEquiv (G.publicOf i observation)) =
        K.publicOf i
          (f.observationEquiv i
            (e.observationEquiv i observation))
    rw [e.map_publicOf, f.map_publicOf]
  infoStateEquiv := fun i =>
    (e.infoStateEquiv i).trans (f.infoStateEquiv i)
  map_infoObserve := by
    intro i information
    change
      f.observationEquiv i
          (e.observationEquiv i
            (G.infoObserve i information)) =
        K.infoObserve i
          (f.infoStateEquiv i
            (e.infoStateEquiv i information))
    rw [e.map_infoObserve, f.map_infoObserve]
  infoActionEquiv := fun i information =>
    (e.infoActionEquiv i information).trans
      (f.infoActionEquiv i
        (e.infoStateEquiv i information))
  map_infoAt := by
    intro history i hsource htarget
    let hmiddle :
        H.base.mover
            (e.historyIso.stateEquiv history).1 =
          some i := by
      rw [e.map_mover history]
      exact hsource
    exact e.transInfoAt f history i hsource hmiddle htarget
  map_infoActionAt := by
    intro history i hsource htarget action
    let middleHistory :=
      e.historyIso.stateEquiv history
    let hmiddle :
        H.base.mover middleHistory.1 = some i := by
      rw [e.map_mover history]
      exact hsource
    let sourceInformation :=
      G.infoAt history i hsource
    let middleInformation :=
      H.infoAt middleHistory i hmiddle
    have hFirst :
        e.infoStateEquiv i sourceInformation =
          middleInformation :=
      e.map_infoAt history i hsource hmiddle
    have hSecond :
        f.infoStateEquiv i middleInformation =
          K.infoAt
            (f.historyIso.stateEquiv middleHistory)
            i htarget :=
      f.map_infoAt middleHistory i hmiddle htarget
    let middleAction :=
      cast
        (congrArg (H.InfoAction i) hFirst)
        (e.infoActionEquiv i sourceInformation action)
    let targetAction :=
      cast
        (congrArg (K.InfoAction i) hSecond)
        (f.infoActionEquiv i middleInformation middleAction)
    have hcast :
        cast
            (congrArg (K.InfoAction i)
              (e.transInfoAt f history i
                hsource hmiddle htarget))
            (f.infoActionEquiv i
              (e.infoStateEquiv i sourceInformation)
              (e.infoActionEquiv i sourceInformation action)) =
          targetAction := by
      exact
        Equiv.fiberEquivAt_trans_apply
          (W := G.InfoAction i)
          (Z := H.InfoAction i)
          (V := K.InfoAction i)
          (e.infoStateEquiv i)
          (f.infoStateEquiv i)
          (e.infoActionEquiv i)
          (f.infoActionEquiv i)
          sourceInformation middleInformation
          (K.infoAt
            (f.historyIso.stateEquiv middleHistory)
            i htarget)
          hFirst hSecond action
    change
      K.actionEquiv
          (f.historyIso.stateEquiv middleHistory)
          i htarget
          (cast
            (congrArg (K.InfoAction i)
              (e.transInfoAt f history i
                hsource hmiddle htarget))
            (f.infoActionEquiv i
              (e.infoStateEquiv i sourceInformation)
              (e.infoActionEquiv i sourceInformation action))) =
        f.historyIso.actionEquiv middleHistory
          (e.historyIso.actionEquiv history
            (G.actionEquiv history i hsource action))
    rw [hcast]
    calc
      K.actionEquiv
          (f.historyIso.stateEquiv middleHistory)
          i htarget targetAction =
        f.historyIso.actionEquiv middleHistory
          (H.actionEquiv middleHistory i hmiddle
            middleAction) := by
              exact
                f.map_infoActionAt
                  middleHistory i hmiddle htarget middleAction
      _ = f.historyIso.actionEquiv middleHistory
          (e.historyIso.actionEquiv history
            (G.actionEquiv history i hsource action)) := by
              exact congrArg
                (f.historyIso.actionEquiv middleHistory)
                (e.map_infoActionAt
                  history i hsource hmiddle action)

/-- Strict composition preserves exact external-root correspondence. -/
theorem trans_preservesRootPresentations
    {K : ControlledObservedGame N}
    (e : G.Iso H) (f : H.Iso K)
    {sourceRoots : G.ContinuationRootPresentation}
    {middleRoots : H.ContinuationRootPresentation}
    {targetRoots : K.ContinuationRootPresentation}
    (he : e.PreservesRootPresentations sourceRoots middleRoots)
    (hf : f.PreservesRootPresentations middleRoots targetRoots) :
    (e.trans f).PreservesRootPresentations
      sourceRoots targetRoots := by
  intro history
  exact (he history).trans
    (hf (e.historyIso.stateEquiv history))

/-! ### Inverse strict isomorphisms -/

/-- Inverse equivalence of one dependent information-action fiber. -/
def inverseInfoActionEquiv
    (e : G.Iso H) (i : N)
    (targetInformation : H.InfoState i) :
    H.InfoAction i targetInformation ≃
      G.InfoAction i
        ((e.infoStateEquiv i).symm targetInformation) :=
  (Equiv.cast
      (congrArg (H.InfoAction i)
        ((e.infoStateEquiv i).apply_symm_apply
          targetInformation))).symm.trans
    (e.infoActionEquiv i
      ((e.infoStateEquiv i).symm targetInformation)).symm

/-- Reverse the information square at one mapped history. -/
theorem inverseInfoAt
    (e : G.Iso H)
    (history : G.base.History) (i : N)
    (hsource : G.base.mover history.1 = some i)
    (htarget :
      H.base.mover
          (e.historyIso.stateEquiv history).1 = some i) :
    (e.infoStateEquiv i).symm
        (H.infoAt
          (e.historyIso.stateEquiv history) i htarget) =
      G.infoAt history i hsource := by
  apply (e.infoStateEquiv i).injective
  simpa using
    (e.map_infoAt history i hsource htarget).symm

private theorem cast_inverseFiber
    {α β : Type*} {W : α → Type*} {Z : β → Type*}
    (base : α ≃ β)
    (fiber : ∀ source, W source ≃ Z (base source))
    (source sourceBack : α) (target : β)
    (hforward : base source = target)
    (hright : base sourceBack = target)
    (hleft : sourceBack = source)
    (value : Z target) :
    cast (congrArg W hleft)
        ((fiber sourceBack).symm
          (cast (congrArg Z hright).symm value)) =
      (fiber source).symm
        (cast (congrArg Z hforward).symm value) := by
  subst sourceBack
  rfl

private theorem cast_inverseInfoActionEquiv
    (e : G.Iso H) (i : N)
    (sourceInformation : G.InfoState i)
    (targetInformation : H.InfoState i)
    (hforward :
      e.infoStateEquiv i sourceInformation =
        targetInformation)
    (hback :
      (e.infoStateEquiv i).symm targetInformation =
        sourceInformation)
    (action : H.InfoAction i targetInformation) :
    cast
        (congrArg (G.InfoAction i) hback)
        (e.inverseInfoActionEquiv i targetInformation action) =
      (e.infoActionEquiv i sourceInformation).symm
        (cast
          (congrArg (H.InfoAction i) hforward).symm
          action) := by
  exact
    cast_inverseFiber
      (e.infoStateEquiv i) (e.infoActionEquiv i)
      sourceInformation
      ((e.infoStateEquiv i).symm targetInformation)
      targetInformation hforward
      ((e.infoStateEquiv i).apply_symm_apply targetInformation)
      hback action

private theorem cast_inverseHistoryActionEquiv
    {A B : Arena} (e : A.Iso B)
    (source : A.State) (target : B.State)
    (hforward : e.stateEquiv source = target)
    (hback : e.stateEquiv.symm target = source)
    (action : B.Action target) :
    cast (congrArg A.Action hback)
        (e.inverseActionEquiv target action) =
      (e.actionEquiv source).symm
        (cast (congrArg B.Action hforward).symm action) := by
  exact
    cast_inverseFiber e.stateEquiv e.actionEquiv
      source (e.stateEquiv.symm target) target
      hforward (e.stateEquiv.apply_symm_apply target)
      hback action

private theorem actionEquiv_heq_of_history_eq
    (G : ControlledObservedGame N) (i : N)
    {first second : G.base.History}
    (hhistory : first = second)
    (hfirst : G.base.mover first.1 = some i)
    (hsecond : G.base.mover second.1 = some i)
    (firstAction :
      G.InfoAction i (G.infoAt first i hfirst))
    (secondAction :
      G.InfoAction i (G.infoAt second i hsecond))
    (haction : firstAction ≍ secondAction) :
    G.actionEquiv first i hfirst firstAction ≍
      G.actionEquiv second i hsecond secondAction := by
  subst second
  have hmover : hsecond = hfirst :=
    Subsingleton.elim _ _
  cases hmover
  cases haction
  rfl

private theorem inverse_infoActionAt
    (e : G.Iso H)
    (history : G.base.History) (i : N)
    (hsource : G.base.mover history.1 = some i)
    (htarget :
      H.base.mover
          (e.historyIso.stateEquiv history).1 = some i)
    (action :
      H.InfoAction i
        (H.infoAt
          (e.historyIso.stateEquiv history) i htarget)) :
    G.actionEquiv history i hsource
        (cast
          (congrArg (G.InfoAction i)
            (e.inverseInfoAt history i hsource htarget))
          (e.inverseInfoActionEquiv i
            (H.infoAt
              (e.historyIso.stateEquiv history) i htarget)
            action)) =
      cast
        (congrArg G.base.unfold.Action
          (e.historyIso.stateEquiv.symm_apply_apply history))
        (e.historyIso.inverseActionEquiv
            (e.historyIso.stateEquiv history)
          (H.actionEquiv
            (e.historyIso.stateEquiv history)
            i htarget action)) := by
  have hinfo :
      e.infoStateEquiv i (G.infoAt history i hsource) =
        H.infoAt
          (e.historyIso.stateEquiv history) i htarget :=
    e.map_infoAt history i hsource htarget
  rw [cast_inverseInfoActionEquiv e i
    (G.infoAt history i hsource)
    (H.infoAt
      (e.historyIso.stateEquiv history) i htarget)
    hinfo (e.inverseInfoAt history i hsource htarget)]
  rw [cast_inverseHistoryActionEquiv e.historyIso
    history (e.historyIso.stateEquiv history)
    rfl (e.historyIso.stateEquiv.symm_apply_apply history)]
  apply (e.historyIso.actionEquiv history).injective
  simpa using
    (e.map_infoActionAt history i hsource htarget
      ((e.infoActionEquiv i
        (G.infoAt history i hsource)).symm
          (cast
            (congrArg (H.InfoAction i) hinfo).symm
            action))).symm

/-- Reverse a strict payoff-free observed-game isomorphism. -/
def symm (e : G.Iso H) : H.Iso G where
  historyIso := e.historyIso.symm
  map_init := by
    change
      e.historyIso.stateEquiv.symm
          (Arena.HistoryFrom.nil
            H.base.toArena H.base.init) =
        Arena.HistoryFrom.nil G.base.toArena G.base.init
    apply e.historyIso.stateEquiv.injective
    rw [e.historyIso.stateEquiv.apply_symm_apply, e.map_init]
  map_mover := by
    intro history
    simpa using
      (e.map_mover
        (e.historyIso.stateEquiv.symm history)).symm
  observationEquiv := fun i => (e.observationEquiv i).symm
  map_observe := by
    intro i history
    apply (e.observationEquiv i).injective
    simpa using
      (e.map_observe i
        (e.historyIso.stateEquiv.symm history)).symm
  publicEquiv := e.publicEquiv.symm
  map_publicObserve := by
    intro history
    apply e.publicEquiv.injective
    simpa using
      (e.map_publicObserve
        (e.historyIso.stateEquiv.symm history)).symm
  map_publicOf := by
    intro i observation
    apply e.publicEquiv.injective
    simpa using
      (e.map_publicOf i
        ((e.observationEquiv i).symm observation)).symm
  infoStateEquiv := fun i => (e.infoStateEquiv i).symm
  map_infoObserve := by
    intro i information
    apply (e.observationEquiv i).injective
    simpa using
      (e.map_infoObserve i
        ((e.infoStateEquiv i).symm information)).symm
  infoActionEquiv := e.inverseInfoActionEquiv
  map_infoAt := by
    intro history
    obtain ⟨sourceHistory, rfl⟩ :=
      e.historyIso.stateEquiv.surjective history
    intro i hsource htarget
    have htarget' :
        G.base.mover sourceHistory.1 = some i := by
      simpa [Arena.Iso.symm] using htarget
    simpa [Arena.Iso.symm] using
      e.inverseInfoAt sourceHistory i htarget' hsource
  map_infoActionAt := by
    intro history
    obtain ⟨sourceHistory, rfl⟩ :=
      e.historyIso.stateEquiv.surjective history
    intro i hsource htarget action
    have htarget' :
        G.base.mover sourceHistory.1 = some i := by
      simpa [Arena.Iso.symm] using htarget
    have hcore :=
      e.inverse_infoActionAt
        sourceHistory i htarget' hsource action
    apply eq_of_heq
    refine HEq.trans ?_ ((heq_iff_eq.mpr hcore).trans ?_)
    · apply actionEquiv_heq_of_history_eq G i
        (e.historyIso.stateEquiv.symm_apply_apply sourceHistory)
        htarget htarget'
      exact
        (cast_heq _ _).trans
          (cast_heq _ _).symm
    · exact cast_heq _ _

/-- Inverting exact root correspondence reverses its direction. -/
theorem symm_preservesRootPresentations
    (e : G.Iso H)
    {sourceRoots : G.ContinuationRootPresentation}
    {targetRoots : H.ContinuationRootPresentation}
    (hroots :
      e.PreservesRootPresentations sourceRoots targetRoots) :
    e.symm.PreservesRootPresentations
      targetRoots sourceRoots := by
  intro targetHistory
  let sourceHistory :=
    e.historyIso.stateEquiv.symm targetHistory
  have hmap :
      e.historyIso.stateEquiv sourceHistory =
        targetHistory :=
    e.historyIso.stateEquiv.apply_symm_apply targetHistory
  simpa [symm, sourceHistory, hmap] using
    (hroots sourceHistory).symm

/-- Identity is a left unit for strict composition. -/
@[simp]
theorem refl_trans (e : G.Iso H) :
    (refl G).trans e = e := by
  apply Iso.ext
  · exact Arena.Iso.refl_trans e.historyIso
  · funext i
    apply Equiv.ext
    intro observation
    rfl
  · apply Equiv.ext
    intro observation
    rfl
  · funext i
    apply Equiv.ext
    intro information
    rfl
  · apply heq_of_eq
    funext i information
    apply Equiv.ext
    intro action
    rfl

/-- Identity is a right unit for strict composition. -/
@[simp]
theorem trans_refl (e : G.Iso H) :
    e.trans (refl H) = e := by
  apply Iso.ext
  · exact Arena.Iso.trans_refl e.historyIso
  · funext i
    apply Equiv.ext
    intro observation
    rfl
  · apply Equiv.ext
    intro observation
    rfl
  · funext i
    apply Equiv.ext
    intro information
    rfl
  · apply heq_of_eq
    funext i information
    apply Equiv.ext
    intro action
    rfl

/-- Strict composition is associative. -/
theorem trans_assoc
    {K L : ControlledObservedGame N}
    (e : G.Iso H) (f : H.Iso K) (g : K.Iso L) :
    (e.trans f).trans g = e.trans (f.trans g) := by
  apply Iso.ext
  · exact Arena.Iso.trans_assoc
      e.historyIso f.historyIso g.historyIso
  · funext i
    apply Equiv.ext
    intro observation
    rfl
  · apply Equiv.ext
    intro observation
    rfl
  · funext i
    apply Equiv.ext
    intro information
    rfl
  · apply heq_of_eq
    funext i information
    apply Equiv.ext
    intro action
    rfl

end Iso

end ExtensiveGame.ControlledObservedGame
