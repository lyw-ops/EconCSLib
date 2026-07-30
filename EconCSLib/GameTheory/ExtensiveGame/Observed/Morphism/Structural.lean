/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Fiber
import EconCSLib.GameTheory.ExtensiveGame.Observed.Game
import EconCSLib.GameTheory.GameForm.Basic

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Structural

Strict observed-EFG isomorphisms, mapping, identity, and composition.
-/

namespace ExtensiveGame.ObservedGame

universe uV

variable {N U : Type*}

/-- A strict structural isomorphism of history-indexed observed EFGs.

`historyIso` is an Arena isomorphism between the two history unfoldings.
Consequently, history nodes and the legal dependent action type at each node
are both related by actual equivalences, and one source step is exactly one
target step.  The remaining fields make all game-theoretic structure commute
with that strict tree isomorphism. -/
structure Iso (G H : ObservedGame N U) where
  /-- Strict isomorphism of the complete-history Arenas. -/
  historyIso : G.base.unfold.toArena.Iso H.base.unfold.toArena
  /-- The empty histories correspond. -/
  map_init :
    historyIso.stateEquiv
        (Arena.HistoryFrom.nil G.base.toArena G.base.init) =
      Arena.HistoryFrom.nil H.base.toArena H.base.init
  /-- Strategic movers agree at corresponding histories. -/
  map_mover :
    ∀ h : G.base.toArena.HistoryFrom G.base.init,
      H.base.mover (historyIso.stateEquiv h).1 =
        G.base.mover h.1
  /-- Terminal payoff vectors agree at corresponding histories. -/
  map_payoff :
    ∀ h : G.base.toArena.HistoryFrom G.base.init,
      G.base.isTerminal h.1 →
      H.base.payoff (historyIso.stateEquiv h).1 =
        G.base.payoff h.1
  /-- Equivalence of each player's all-history observation type. -/
  observationEquiv :
    (i : N) → G.Observation i ≃ H.Observation i
  /-- Private observations commute with history mapping. -/
  map_observe :
    ∀ (i : N) (h : G.base.toArena.HistoryFrom G.base.init),
      observationEquiv i (G.observe i h) =
        H.observe i (historyIso.stateEquiv h)
  /-- Equivalence of public observation, or public-state, types. -/
  publicEquiv :
    G.PublicObservation ≃ H.PublicObservation
  /-- Public observations commute with history mapping. -/
  map_publicObserve :
    ∀ h : G.base.toArena.HistoryFrom G.base.init,
      publicEquiv (G.publicObserve h) =
        H.publicObserve (historyIso.stateEquiv h)
  /-- Forgetting private information to its public component commutes. -/
  map_publicOf :
    ∀ (i : N) (observation : G.Observation i),
      publicEquiv (G.publicOf i observation) =
        H.publicOf i (observationEquiv i observation)
  /-- Equivalence of each player's decision information-state type. -/
  infoStateEquiv :
    (i : N) → G.InfoState i ≃ H.InfoState i
  /-- Decision information carries the corresponding private observation. -/
  map_infoObserve :
    ∀ (i : N) (information : G.InfoState i),
      observationEquiv i (G.infoObserve i information) =
        H.infoObserve i (infoStateEquiv i information)
  /-- Corresponding information states have equivalent indexed abstract
  actions. -/
  infoActionEquiv :
    ∀ (i : N) (information : G.InfoState i),
      G.InfoAction i information ≃
        H.InfoAction i (infoStateEquiv i information)
  /-- The decision information state at a mapped player history is the mapped
  source information state. -/
  map_infoAt :
    ∀ (h : G.base.toArena.HistoryFrom G.base.init) (i : N)
      (hsource : G.base.mover h.1 = some i)
      (htarget :
        H.base.mover (historyIso.stateEquiv h).1 = some i),
      infoStateEquiv i (G.infoAt h i hsource) =
        H.infoAt (historyIso.stateEquiv h) i htarget
  /-- Mapping an arbitrary abstract information action and then realizing it
  as a concrete legal action agrees exactly with mapping the realized source
  action through the history-Arena action equivalence.

  This is the local, strategy-independent coherence square.  It is stated
  separately from `map_actionAt` because behavioral strategies must transport
  every action in the support of a local `PMF`, even when a complete pure
  strategy profile need not exist. -/
  map_infoActionAt :
    ∀ (h : G.base.toArena.HistoryFrom G.base.init) (i : N)
      (hsource : G.base.mover h.1 = some i)
      (htarget :
        H.base.mover (historyIso.stateEquiv h).1 = some i)
      (action : G.InfoAction i (G.infoAt h i hsource)),
      H.actionEquiv (historyIso.stateEquiv h) i htarget
          (cast
            (congrArg (H.InfoAction i)
              (map_infoAt h i hsource htarget))
            (infoActionEquiv i (G.infoAt h i hsource) action)) =
        historyIso.actionEquiv h
          (G.actionEquiv h i hsource action)
  /-- Presentation-designated continuation roots correspond exactly. -/
  map_designatedContinuationRoot :
    ∀ h : G.base.toArena.HistoryFrom G.base.init,
      G.IsDesignatedContinuationRoot h ↔
        H.IsDesignatedContinuationRoot (historyIso.stateEquiv h)

namespace Iso

variable {G H : ObservedGame N U}

/-- Strict observed-game isomorphisms are determined by their structural
equivalences; all commuting-square fields are propositions. -/
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

/-- Strict Arena morphisms preserve reachability. -/
private theorem mapReachable
    {A B : Arena} (f : A.Hom B) {source target : A.State}
    (h : Arena.Reachable A source target) :
    Arena.Reachable B (f.state source) (f.state target) := by
  induction h with
  | refl =>
      exact Arena.Reachable.refl _
  | @step source next action h ih =>
      refine Arena.Reachable.step (f.action source action) ?_
      rw [← f.map_next source action]
      exact ih

/-- Strict observed-game isomorphisms preserve and reflect the complete-history
extension relation used by lawful subgame systems. -/
theorem map_isContinuationOf
    (e : G.Iso H)
    (root current :
      G.base.toArena.HistoryFrom G.base.init) :
    G.IsContinuationOf root current ↔
      H.IsContinuationOf
        (e.historyIso.stateEquiv root)
        (e.historyIso.stateEquiv current) := by
  constructor
  · exact mapReachable e.historyIso.toHom
  · intro htarget
    have hsource :=
      mapReachable e.historyIso.symm.toHom htarget
    change
      Arena.Reachable G.base.unfold.toArena
        (e.historyIso.stateEquiv.symm
          (e.historyIso.stateEquiv root))
        (e.historyIso.stateEquiv.symm
          (e.historyIso.stateEquiv current))
      at hsource
    change Arena.Reachable G.base.unfold.toArena root current
    simpa only [Equiv.symm_apply_apply] using hsource

/-- The pure-strategy equivalence induced by the information-state and
information-action equivalences. -/
def strategyEquiv (e : G.Iso H) (i : N) :
    G.PureStrategy i ≃ H.PureStrategy i :=
  (e.infoStateEquiv i).piCongr (e.infoActionEquiv i)

/-- The information-action equivalence at a pair of corresponding player
histories.

The equality between the mapped source information state and the target's
actual `infoAt` index is encapsulated here.  This keeps dependent transports
stable across pure, behavioral, inverse, and composition APIs. -/
def infoActionEquivAt
    (e : G.Iso H)
    (history : G.base.toArena.HistoryFrom G.base.init)
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
    (history : G.base.toArena.HistoryFrom G.base.init)
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

/-- Realization of the cast-stable local information-action equivalence
commutes with the strict history-action equivalence. -/
theorem map_infoActionEquivAt
    (e : G.Iso H)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hsource : G.base.mover history.1 = some i)
    (htarget :
      H.base.mover (e.historyIso.stateEquiv history).1 = some i)
    (action : G.InfoAction i (G.infoAt history i hsource)) :
    H.actionEquiv (e.historyIso.stateEquiv history) i htarget
        (e.infoActionEquivAt history i hsource htarget action) =
      e.historyIso.actionEquiv history
        (G.actionEquiv history i hsource action) :=
  e.map_infoActionAt history i hsource htarget action

/-- Mapping a local action and immediately applying the inverse local
equivalence returns the source action. -/
@[simp]
theorem infoActionEquivAt_symm_apply_apply
    (e : G.Iso H)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hsource : G.base.mover history.1 = some i)
    (htarget :
      H.base.mover (e.historyIso.stateEquiv history).1 = some i)
    (action : G.InfoAction i (G.infoAt history i hsource)) :
    (e.infoActionEquivAt history i hsource htarget).symm
        (e.infoActionEquivAt history i hsource htarget action) =
      action :=
  (e.infoActionEquivAt history i hsource htarget).symm_apply_apply action

/-- Applying the inverse local equivalence and mapping forward returns the
target action. -/
@[simp]
theorem infoActionEquivAt_apply_symm_apply
    (e : G.Iso H)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hsource : G.base.mover history.1 = some i)
    (htarget :
      H.base.mover (e.historyIso.stateEquiv history).1 = some i)
    (action :
      H.InfoAction i
        (H.infoAt (e.historyIso.stateEquiv history) i htarget)) :
    e.infoActionEquivAt history i hsource htarget
        ((e.infoActionEquivAt
          history i hsource htarget).symm action) =
      action :=
  (e.infoActionEquivAt history i hsource htarget).apply_symm_apply action

/-- Map a complete pure profile along an observed-EFG isomorphism. -/
def mapProfile (e : G.Iso H) (profile : G.PureProfile) :
    H.PureProfile :=
  fun i => e.strategyEquiv i (profile i)

/-- Map a target pure profile back through the strategy equivalences. -/
def unmapProfile (e : G.Iso H) (profile : H.PureProfile) :
    G.PureProfile :=
  fun i => (e.strategyEquiv i).symm (profile i)

@[simp]
theorem mapProfile_apply (e : G.Iso H) (profile : G.PureProfile) (i : N) :
    e.mapProfile profile i = e.strategyEquiv i (profile i) := rfl

@[simp]
theorem unmapProfile_apply (e : G.Iso H) (profile : H.PureProfile) (i : N) :
    e.unmapProfile profile i = (e.strategyEquiv i).symm (profile i) := rfl

@[simp]
theorem mapProfile_unmapProfile (e : G.Iso H) (profile : H.PureProfile) :
    e.mapProfile (e.unmapProfile profile) = profile := by
  funext i
  exact (e.strategyEquiv i).apply_symm_apply (profile i)

@[simp]
theorem unmapProfile_mapProfile (e : G.Iso H) (profile : G.PureProfile) :
    e.unmapProfile (e.mapProfile profile) = profile := by
  funext i
  exact (e.strategyEquiv i).symm_apply_apply (profile i)

/-- Mapping a pure profile and then selecting its concrete action agrees
exactly with mapping the source concrete action through the history-Arena
action equivalence.

This is derived from the strategy-independent local information-action
coherence square, rather than stored as a redundant isomorphism field. -/
theorem map_actionAt
    (e : G.Iso H)
    (profile : G.PureProfile)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hsource : G.base.mover history.1 = some i)
    (htarget :
      H.base.mover (e.historyIso.stateEquiv history).1 = some i) :
    PureProfile.actionAt H
        (e.mapProfile profile)
        (e.historyIso.stateEquiv history) i htarget =
      e.historyIso.actionEquiv history
        (PureProfile.actionAt G profile history i hsource) := by
  unfold PureProfile.actionAt PureStrategy.actionAt
  have hinfo :
      e.infoStateEquiv i (G.infoAt history i hsource) =
        H.infoAt (e.historyIso.stateEquiv history) i htarget :=
    e.map_infoAt history i hsource htarget
  have hchoice :
      e.mapProfile profile i
          (H.infoAt
            (e.historyIso.stateEquiv history) i htarget) =
        e.infoActionEquivAt history i hsource htarget
          (profile i (G.infoAt history i hsource)) := by
    rw [infoActionEquivAt_apply]
    exact
      Equiv.piCongr_apply_of_eq
        (W := G.InfoAction i)
        (Z := H.InfoAction i)
        (e.infoStateEquiv i)
        (e.infoActionEquiv i)
        (profile i)
        (G.infoAt history i hsource)
        (H.infoAt
          (e.historyIso.stateEquiv history) i htarget)
        hinfo
  rw [hchoice]
  exact
    e.map_infoActionEquivAt history i hsource htarget
      (profile i (G.infoAt history i hsource))

/-- Identity strict structural isomorphism of an observed EFG. -/
def refl (G : ObservedGame N U) : G.Iso G where
  historyIso := Arena.Iso.refl G.base.unfold.toArena
  map_init := rfl
  map_mover := by
    intro h
    rfl
  map_payoff := by
    intro h _
    rfl
  observationEquiv := fun _ => Equiv.refl _
  map_observe := by
    intro i h
    rfl
  publicEquiv := Equiv.refl _
  map_publicObserve := by
    intro h
    rfl
  map_publicOf := by
    intro i observation
    rfl
  infoStateEquiv := fun _ => Equiv.refl _
  map_infoObserve := by
    intro i information
    rfl
  infoActionEquiv := fun _ _ => Equiv.refl _
  map_infoAt := by
    intro h i hsource htarget
    congr
  map_infoActionAt := by
    intro h i hsource htarget action
    rfl
  map_designatedContinuationRoot := by
    intro h
    rfl

/-- Identity isomorphisms leave local information actions unchanged, including
the proof-irrelevant mover-index transport. -/
@[simp]
theorem refl_infoActionEquivAt
    (history : G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hsource htarget : G.base.mover history.1 = some i)
    (action : G.InfoAction i (G.infoAt history i hsource)) :
    (refl G).infoActionEquivAt
        history i hsource htarget action =
      action := by
  rfl

/-- Identity isomorphisms leave pure profiles unchanged. -/
@[simp]
theorem refl_mapProfile (profile : G.PureProfile) :
    (refl G).mapProfile profile = profile := by
  funext i information
  change
    ((Equiv.refl (G.InfoState i)).piCongr
      (fun state => Equiv.refl (G.InfoAction i state)))
        (profile i) information =
      profile i information
  simpa using
    Equiv.piCongr_apply_apply
      (Equiv.refl (G.InfoState i))
      (fun state => Equiv.refl (G.InfoAction i state))
      (profile i) information

/-- The information-state equality used by composition of strict observed-EFG
isomorphisms. -/
def transInfoAt {K : ObservedGame N U}
    (e : G.Iso H) (f : H.Iso K)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hsource : G.base.mover history.1 = some i)
    (hmiddle :
      H.base.mover (e.historyIso.stateEquiv history).1 = some i)
    (htarget :
      K.base.mover
        (f.historyIso.stateEquiv
          (e.historyIso.stateEquiv history)).1 =
        some i) :
    (e.infoStateEquiv i).trans (f.infoStateEquiv i)
        (G.infoAt history i hsource) =
      K.infoAt
        (f.historyIso.stateEquiv
          (e.historyIso.stateEquiv history))
        i htarget :=
  (congrArg (f.infoStateEquiv i)
    (e.map_infoAt history i hsource hmiddle)).trans
      (f.map_infoAt
        (e.historyIso.stateEquiv history)
        i hmiddle htarget)

/-- Compose strict structural isomorphisms of observed EFGs. -/
def trans {K : ObservedGame N U}
    (e : G.Iso H) (f : H.Iso K) :
    G.Iso K where
  historyIso := e.historyIso.trans f.historyIso
  map_init := by
    calc
      f.historyIso.stateEquiv
          (e.historyIso.stateEquiv
            (Arena.HistoryFrom.nil
              G.base.toArena G.base.init)) =
        f.historyIso.stateEquiv
          (Arena.HistoryFrom.nil
            H.base.toArena H.base.init) :=
              congrArg f.historyIso.stateEquiv e.map_init
      _ = Arena.HistoryFrom.nil
          K.base.toArena K.base.init :=
            f.map_init
  map_mover := by
    intro history
    change
      K.base.mover
          (f.historyIso.stateEquiv
            (e.historyIso.stateEquiv history)).1 =
        G.base.mover history.1
    rw [f.map_mover, e.map_mover]
  map_payoff := by
    intro history hterminal
    have hmiddleTerminal :
        H.base.isTerminal
          (e.historyIso.stateEquiv history).1 :=
      (e.historyIso.isTerminal_iff history).mp hterminal
    change
      K.base.payoff
          (f.historyIso.stateEquiv
            (e.historyIso.stateEquiv history)).1 =
        G.base.payoff history.1
    rw [f.map_payoff _ hmiddleTerminal,
      e.map_payoff history hterminal]
  observationEquiv := fun i =>
    (e.observationEquiv i).trans
      (f.observationEquiv i)
  map_observe := by
    intro i history
    change
      f.observationEquiv i
          (e.observationEquiv i
            (G.observe i history)) =
        K.observe i
          (f.historyIso.stateEquiv
            (e.historyIso.stateEquiv history))
    rw [e.map_observe, f.map_observe]
  publicEquiv := e.publicEquiv.trans f.publicEquiv
  map_publicObserve := by
    intro history
    change
      f.publicEquiv
          (e.publicEquiv
            (G.publicObserve history)) =
        K.publicObserve
          (f.historyIso.stateEquiv
            (e.historyIso.stateEquiv history))
    rw [e.map_publicObserve, f.map_publicObserve]
  map_publicOf := by
    intro i observation
    change
      f.publicEquiv
          (e.publicEquiv
            (G.publicOf i observation)) =
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
    exact
      e.transInfoAt f history i
        hsource hmiddle htarget
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
        (f.infoActionEquiv i middleInformation
          middleAction)
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
                  middleHistory i hmiddle htarget
                  middleAction
      _ = f.historyIso.actionEquiv middleHistory
          (e.historyIso.actionEquiv history
            (G.actionEquiv history i hsource action)) := by
              exact congrArg
                (f.historyIso.actionEquiv middleHistory)
                (e.map_infoActionAt
                  history i hsource hmiddle action)
  map_designatedContinuationRoot := by
    intro history
    exact
      (e.map_designatedContinuationRoot history).trans
        (f.map_designatedContinuationRoot
          (e.historyIso.stateEquiv history))

/-- The cast-stable local action equivalence is functorial under composition
of strict observed-game isomorphisms. -/
theorem trans_infoActionEquivAt {K : ObservedGame N U}
    (e : G.Iso H) (f : H.Iso K)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hsource : G.base.mover history.1 = some i)
    (hmiddle :
      H.base.mover (e.historyIso.stateEquiv history).1 = some i)
    (htarget :
      K.base.mover
          (f.historyIso.stateEquiv
            (e.historyIso.stateEquiv history)).1 =
        some i)
    (action : G.InfoAction i (G.infoAt history i hsource)) :
    (e.trans f).infoActionEquivAt
        history i hsource htarget action =
      f.infoActionEquivAt
        (e.historyIso.stateEquiv history)
        i hmiddle htarget
        (e.infoActionEquivAt
          history i hsource hmiddle action) := by
  simpa [infoActionEquivAt, trans, transInfoAt] using
    Equiv.fiberEquivAt_trans_apply
      (e.infoStateEquiv i)
      (f.infoStateEquiv i)
      (e.infoActionEquiv i)
      (f.infoActionEquiv i)
      (G.infoAt history i hsource)
      (H.infoAt
        (e.historyIso.stateEquiv history) i hmiddle)
      (K.infoAt
        (f.historyIso.stateEquiv
          (e.historyIso.stateEquiv history))
        i htarget)
      (e.map_infoAt history i hsource hmiddle)
      (f.map_infoAt
        (e.historyIso.stateEquiv history)
        i hmiddle htarget)
      action

/-- Mapping pure profiles is functorial under composition. -/
@[simp]
theorem trans_mapProfile {K : ObservedGame N U}
    (e : G.Iso H) (f : H.Iso K)
    (profile : G.PureProfile) :
    (e.trans f).mapProfile profile =
      f.mapProfile (e.mapProfile profile) := by
  funext i targetInformation
  obtain ⟨middleInformation, rfl⟩ :=
    (f.infoStateEquiv i).surjective targetInformation
  obtain ⟨sourceInformation, rfl⟩ :=
    (e.infoStateEquiv i).surjective middleInformation
  change
    (((e.infoStateEquiv i).trans (f.infoStateEquiv i)).piCongr
      (fun information =>
        (e.infoActionEquiv i information).trans
          (f.infoActionEquiv i
            (e.infoStateEquiv i information))))
      (profile i)
      (f.infoStateEquiv i
        (e.infoStateEquiv i sourceInformation)) =
    (f.infoStateEquiv i).piCongr (f.infoActionEquiv i)
      ((e.infoStateEquiv i).piCongr
        (e.infoActionEquiv i) (profile i))
      (f.infoStateEquiv i
        (e.infoStateEquiv i sourceInformation))
  rw [Equiv.piCongr_apply_apply,
    Equiv.piCongr_apply_apply]
  simpa using
    Equiv.piCongr_apply_apply
      ((e.infoStateEquiv i).trans (f.infoStateEquiv i))
      (fun information =>
        (e.infoActionEquiv i information).trans
          (f.infoActionEquiv i
            (e.infoStateEquiv i information)))
      (profile i) sourceInformation

/-- Identity is a left unit for strict observed-game isomorphism composition. -/
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

/-- Identity is a right unit for strict observed-game isomorphism
composition. -/
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

/-- Composition of strict observed-game isomorphisms is associative. -/
theorem trans_assoc {K L : ObservedGame N U}
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

end ExtensiveGame.ObservedGame
