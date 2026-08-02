/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.CompletePlay

/-!
# Payoff-free observed controlled games

API role: **canonical carrier**. This is the root of the
`Observed.Controlled` module hierarchy and owns only the base
observation/information record. Semantic and responsibility owners live below
`Observed.Controlled`; payoff-aware adapters are isolated below
`Observed.Controlled.Compat`.

This module is the objective-free information layer for extensive games.
`ControlledObservedGame` combines a `ControlledGame` with private/public
observations, decision information states, and information-indexed actions.
It stores neither payoff nor continuation-root selection.

Continuation roots are supplied by the separate
`ContinuationRootPresentation`; lawful standard subgames remain a stronger,
independent payoff-free certificate in
`Controlled.Infrastructure.Subgame`.

## Main definitions

* `ControlledObservedGame`.
* `ControlledObservedGame.relabelPlayers` and `relabelPureProfileEquiv`.
* `ControlledObservedGame.ContinuationRootPresentation`.
* `ControlledObservedGame.PureStrategy` and `PureProfile`.
* `ControlledObservedGame.completeInformation`.
-/

namespace ExtensiveGame

universe uN uA uS uO uI uP

/-- Observation and decision-information data over a payoff-free controlled
game.

The record deliberately excludes objectives, probability, finiteness, recall,
and continuation-root selection. Two analyses with identical dynamics and
information but different selected roots therefore share exactly the same
`ControlledObservedGame`. -/
structure ControlledObservedGame (N : Type uN) where
  /-- The payoff-free controlled dynamics. -/
  base : ControlledGame.{uN, uS, uA} N
  /-- Player `i`'s current private-observation type. -/
  Observation : N → Type uO
  /-- Public-observation type. -/
  PublicObservation : Type uP
  /-- Player `i`'s private observation after a complete history. -/
  observe :
    (i : N) → base.toArena.HistoryFrom base.init → Observation i
  /-- Public observation after a complete history. -/
  publicObserve :
    base.toArena.HistoryFrom base.init → PublicObservation
  /-- Forget private data and retain its public component. -/
  publicOf : (i : N) → Observation i → PublicObservation
  /-- Every private observation refines the public observation. -/
  observe_public :
    ∀ (i : N) (history : base.toArena.HistoryFrom base.init),
      publicOf i (observe i history) = publicObserve history
  /-- Player `i`'s decision-information carrier. -/
  InfoState : N → Type uI
  /-- Forget decision memory and retain the current private signal. -/
  infoObserve : (i : N) → InfoState i → Observation i
  /-- Decision information at a history controlled by player `i`. -/
  infoAt :
    ∀ (history : base.toArena.HistoryFrom base.init) (i : N),
      base.mover history.1 = some i → InfoState i
  /-- Decision information projects to the current private signal. -/
  infoAt_observe :
    ∀ (history : base.toArena.HistoryFrom base.init) (i : N)
      (hmover : base.mover history.1 = some i),
      infoObserve i (infoAt history i hmover) = observe i history
  /-- Abstract actions at one decision-information state. -/
  InfoAction : (i : N) → InfoState i → Type uA
  /-- Abstract information actions are exactly the legal concrete actions at
  each represented decision history. -/
  actionEquiv :
    ∀ (history : base.toArena.HistoryFrom base.init) (i : N)
      (hmover : base.mover history.1 = some i),
      InfoAction i (infoAt history i hmover) ≃ base.Action history.1

namespace ControlledObservedGame

variable {N M : Type*} (G : ControlledObservedGame N)

/-- Relabel the player carrier along an equivalence while preserving the
Arena, initial state, histories, public observation, and every indexed
information/action fiber.

If `e : M ≃ N`, the result uses `M` as its player type. An old mover `i : N`
is renamed to `e.symm i`; data indexed by a new player `j : M` reuse the old
fiber indexed by `e j`. This is a structural reindexing, not a player
addition/deletion operation. -/
def relabelPlayers (e : M ≃ N) :
    ControlledObservedGame M where
  base :=
    { toArena := G.base.toArena
      init := G.base.init
      mover := fun state => (G.base.mover state).map e.symm }
  Observation := fun i => G.Observation (e i)
  PublicObservation := G.PublicObservation
  observe := fun i history => G.observe (e i) history
  publicObserve := G.publicObserve
  publicOf := fun i observation => G.publicOf (e i) observation
  observe_public := fun i history => G.observe_public (e i) history
  InfoState := fun i => G.InfoState (e i)
  infoObserve := fun i information => G.infoObserve (e i) information
  infoAt := by
    intro history i hmover
    apply G.infoAt history (e i)
    have h := congrArg (Option.map e) hmover
    simpa using h
  infoAt_observe := by
    intro history i hmover
    apply G.infoAt_observe
  InfoAction := fun i information => G.InfoAction (e i) information
  actionEquiv := by
    intro history i hmover
    apply G.actionEquiv

@[simp]
theorem relabelPlayers_toArena
    (e : M ≃ N) :
    (G.relabelPlayers e).base.toArena = G.base.toArena :=
  rfl

@[simp]
theorem relabelPlayers_init
    (e : M ≃ N) :
    (G.relabelPlayers e).base.init = G.base.init :=
  rfl

@[simp]
theorem relabelPlayers_mover
    (e : M ≃ N) (state : G.base.State) :
    (G.relabelPlayers e).base.mover state =
      (G.base.mover state).map e.symm :=
  rfl

@[simp]
theorem relabelPlayers_observe
    (e : M ≃ N) (i : M)
    (history : G.base.toArena.HistoryFrom G.base.init) :
    (G.relabelPlayers e).observe i history =
      G.observe (e i) history :=
  rfl

/-- Caller-selected continuation roots for one payoff-free observed game.

This presentation carries no standard-subgame lawfulness claim. It is
deliberately separate from the observed-game record so changing analysis roots
does not change the identity of the dynamics or information structure. -/
structure ContinuationRootPresentation
    (G : ControlledObservedGame N) where
  /-- Histories exposed to a root-scoped analysis. -/
  IsRoot : G.base.toArena.HistoryFrom G.base.init → Prop
  /-- The initial empty history is always exposed. -/
  init_isRoot :
    IsRoot (Arena.HistoryFrom.nil G.base.toArena G.base.init)

namespace ContinuationRootPresentation

variable {G : ControlledObservedGame N}

/-- Reuse a root presentation after bijective player relabeling.

The Arena and complete-history carrier are definitionally unchanged. -/
def relabelPlayers
    (roots : G.ContinuationRootPresentation)
    (e : M ≃ N) :
    (G.relabelPlayers e).ContinuationRootPresentation where
  IsRoot := roots.IsRoot
  init_isRoot := roots.init_isRoot

@[simp]
theorem relabelPlayers_isRoot
    (roots : G.ContinuationRootPresentation)
    (e : M ≃ N)
    (history : G.base.toArena.HistoryFrom G.base.init) :
    (roots.relabelPlayers e).IsRoot history ↔
      roots.IsRoot history :=
  Iff.rfl

/-- Expose only the initial history. -/
def initialOnly (G : ControlledObservedGame N) :
    G.ContinuationRootPresentation where
  IsRoot := fun history =>
    history = Arena.HistoryFrom.nil G.base.toArena G.base.init
  init_isRoot := rfl

/-- Expose every legal complete history, without claiming that every history
is a lawful standard-subgame root. -/
def allHistories (G : ControlledObservedGame N) :
    G.ContinuationRootPresentation where
  IsRoot := fun _history => True
  init_isRoot := trivial

@[simp]
theorem initialOnly_isRoot_iff
    (history : G.base.toArena.HistoryFrom G.base.init) :
    (initialOnly G).IsRoot history ↔
      history = Arena.HistoryFrom.nil G.base.toArena G.base.init :=
  Iff.rfl

@[simp]
theorem allHistories_isRoot
    (history : G.base.toArena.HistoryFrom G.base.init) :
    (allHistories G).IsRoot history :=
  trivial

end ContinuationRootPresentation

/-- A deterministic contingent plan indexed only by decision information. -/
def PureStrategy (i : N) : Type _ :=
  (information : G.InfoState i) → G.InfoAction i information

/-- A profile of payoff-free pure contingent plans. -/
def PureProfile : Type _ :=
  (i : N) → G.PureStrategy i

/-- Pure profiles are invariant under bijective player renaming, up to the
corresponding dependent-function reindexing. -/
def relabelPureProfileEquiv (e : M ≃ N) :
    (G.relabelPlayers e).PureProfile ≃ G.PureProfile :=
  e.piCongrLeft G.PureStrategy

namespace PureStrategy

/-- Realize an abstract pure action at one represented concrete history. -/
def actionAt {i : N} (strategy : G.PureStrategy i)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (hmover : G.base.mover history.1 = some i) :
    G.base.Action history.1 :=
  G.actionEquiv history i hmover
    (strategy (G.infoAt history i hmover))

end PureStrategy

namespace CompleteInformation

/-- A complete history whose endpoint is controlled by player `i`. -/
abbrev DecisionHistory (base : ControlledGame N) (i : N) :=
  {history : base.toArena.HistoryFrom base.init //
    base.mover history.1 = some i}

/-- Legal actions at a payoff-free complete-information decision history. -/
abbrev DecisionAction (base : ControlledGame N) (i : N)
    (information : DecisionHistory base i) :=
  base.Action information.1.1

end CompleteInformation

/-- Canonical payoff-free complete-information presentation.

Private and public observations retain the complete history. Player `i`'s
information states contain exactly histories whose endpoint mover is `i`, so
chance, other-player, and normalized terminal histories create no spurious
strategy coordinates. -/
abbrev completeInformation (base : ControlledGame N) :
    ControlledObservedGame N where
  base := base
  Observation := fun _i => base.toArena.HistoryFrom base.init
  PublicObservation := base.toArena.HistoryFrom base.init
  observe := fun _i history => history
  publicObserve := fun history => history
  publicOf := fun _i observation => observation
  observe_public := fun _i _history => rfl
  InfoState := CompleteInformation.DecisionHistory base
  infoObserve := fun _i information => information.1
  infoAt := fun history _i hmover => ⟨history, hmover⟩
  infoAt_observe := fun _history _i _hmover => rfl
  InfoAction := CompleteInformation.DecisionAction base
  actionEquiv := fun _history _i _hmover => Equiv.refl _

end ControlledObservedGame

end ExtensiveGame
