/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.StoppedExecution

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.Game

A history-indexed observed extensive-game layer over `ExtensiveGame`.

The base game continues to own states, dependent actions, transitions, movers,
and payoffs.  This wrapper adds an observation for every player at every
history and a public observation at every history.  Player-controlled histories
also map to decision information states, which determine abstract action types.
An explicit equivalence identifies those abstract actions with the legal base
actions.

This indexing makes information-set consistency structural: a pure strategy
has type

```lean
(I : G.InfoState i) → G.InfoAction i I
```

and therefore cannot inspect the concrete history after receiving `I`.

This core module defines player-controlled no-chance execution. The
`Chance` and `Behavior` extension modules add normalized
chance kernels and behavioral strategies without changing the base history or
information-indexed pure-strategy interfaces.

## Main definitions

* `ExtensiveGame.ObservedGame` — observations and information-indexed actions
  over a base extensive game.
* `ObservedGame.historyInformationPresentation` — full-history private
  observation/information with an explicit public projection.
* `ObservedGame.completeInformationPresentation` — the canonical full-history
  observation and information presentation of an ordinary `ExtensiveGame`.
* `ObservedGame.ContinuationRootPresentation.initialOnly` and
  `.allHistories` — explicit, orthogonal choices of presentation-designated
  continuation roots.
* `ObservedGame.PureStrategy` and `PureProfile` — game-bound contingent plans.
* `PureProfile.toHistoryPolicy` — terminal-aware execution of a no-chance
  profile.
* `ObservedGame.IsDesignatedContinuationRoot` — history roots designated by
  the presentation for continuation semantics; lawfulness as standard
  subgames is separate.
* `ObservedGame.IsLawfulSubgameRoot` — the structural proper-root singleton
  and information-closure criterion for one standard-subgame root, with the
  whole-game initial-root convention and independent of presentation
  designation.
* `ObservedGame.SubgameSystem` — an explicit, possibly conservative nonempty
  system of designated lawful roots.
* `ObservedGame.CompleteSubgameSystem` — a `SubgameSystem` whose selected
  roots are exactly all structurally lawful roots.
* `ObservedGame.stoppedHistoryFrom`, `stoppedPayoffFrom`, `stoppedHistory`, and
  `stoppedPayoff` — continuation and root profile semantics.
-/

namespace ExtensiveGame

universe uN uU uA uS uO uI uP

/-- A history-indexed observation and information-action layer over an
extensive game.

`Observation` is defined for every player at every history, including histories
where that player does not move.  `observe_public` says that each player's
observation refines the public observation.  `InfoState` indexes only
player-decision information; `infoAt` and `actionEquiv` are therefore required
only when the history is controlled by the given player. -/
structure ObservedGame (N : Type uN) (U : Type uU) where
  /-- The underlying transition, mover, and payoff data. -/
  base : ExtensiveGame.{uN, uU, uA, uS} N U
  /-- Player `i`'s observation type, defined at every history. -/
  Observation : N → Type uO
  /-- Public observation type. -/
  PublicObservation : Type uP
  /-- Player `i`'s observation after a complete history. -/
  observe :
    (i : N) → base.toArena.HistoryFrom base.init → Observation i
  /-- The public observation after a complete history. -/
  publicObserve :
    base.toArena.HistoryFrom base.init → PublicObservation
  /-- Forget private observation data and retain its public component. -/
  publicOf : (i : N) → Observation i → PublicObservation
  /-- Every player's observation refines the public observation. -/
  observe_public :
    ∀ (i : N) (h : base.toArena.HistoryFrom base.init),
      publicOf i (observe i h) = publicObserve h
  /-- Player `i`'s decision information-state type. -/
  InfoState : N → Type uI
  /-- Project a complete decision-information/memory state to its current
  observable signal.  This map need not be injective: an information state
  may retain memory beyond the current signal. -/
  infoObserve : (i : N) → InfoState i → Observation i
  /-- The decision information state at a history controlled by player `i`. -/
  infoAt :
    ∀ (h : base.toArena.HistoryFrom base.init) (i : N),
      base.mover h.1 = some i → InfoState i
  /-- Decision information projects to the acting player's current
  observation.  This does not assert that `InfoState` contains no additional
  memory. -/
  infoAt_observe :
    ∀ (h : base.toArena.HistoryFrom base.init) (i : N)
      (hmover : base.mover h.1 = some i),
      infoObserve i (infoAt h i hmover) = observe i h
  /-- Abstract actions available at a player information state. -/
  InfoAction : (i : N) → InfoState i → Type uA
  /-- Abstract information-state actions are exactly the legal base actions at
  each player-controlled history represented by that state. -/
  actionEquiv :
    ∀ (h : base.toArena.HistoryFrom base.init) (i : N)
      (hmover : base.mover h.1 = some i),
      InfoAction i (infoAt h i hmover) ≃ base.Action h.1
  /-- Histories designated by this presentation as continuation roots.

  This is explicit data because information-set closure and public-state
  conditions vary between EFG presentations.  The predicate alone carries no
  claim that these are all, or only, the roots of standard proper subgames.
  Standard SPE uses a separate `SubgameSystem` lawfulness certificate. -/
  IsDesignatedContinuationRoot :
    base.toArena.HistoryFrom base.init → Prop
  /-- The initial empty history is always a designated continuation root. -/
  init_isDesignatedContinuationRoot :
    IsDesignatedContinuationRoot
      (Arena.HistoryFrom.nil base.toArena base.init)

namespace ObservedGame

variable {N U : Type*} (G : ObservedGame N U)

/-- Presentation-level selection of designated continuation roots for an
ordinary extensive game.

This is deliberately weaker than `ObservedGame.SubgameSystem`: it records
which roots a presentation exposes, but carries no standard-subgame
lawfulness claim. Keeping it separate from observation data makes the root
choice explicit at every smart-constructor call. -/
structure ContinuationRootPresentation (base : ExtensiveGame N U) where
  /-- Complete histories exposed as continuation roots. -/
  IsRoot : base.toArena.HistoryFrom base.init → Prop
  /-- The initial empty history is always exposed. -/
  init_isRoot :
    IsRoot (Arena.HistoryFrom.nil base.toArena base.init)

namespace ContinuationRootPresentation

variable {base : ExtensiveGame N U}

/-- Root presentations are determined by their root predicate; the initial
root certificate is propositional. -/
@[ext]
theorem ext (first second : ContinuationRootPresentation base)
    (hroot : first.IsRoot = second.IsRoot) :
    first = second := by
  cases first
  cases second
  cases hroot
  rfl

/-- Expose only the initial history as a presentation-designated continuation
root. No later history is selected implicitly. -/
def initialOnly (base : ExtensiveGame N U) :
    ContinuationRootPresentation base where
  IsRoot := fun history =>
    history = Arena.HistoryFrom.nil base.toArena base.init
  init_isRoot := rfl

/-- Expose every legal complete history as a presentation-designated
continuation root.

This does not claim that every history is a lawful standard-subgame root.
Use a `SubgameSystem` (or `CompleteSubgameSystem`) when that stronger semantic
claim is required. -/
def allHistories (base : ExtensiveGame N U) :
    ContinuationRootPresentation base where
  IsRoot := fun _history => True
  init_isRoot := trivial

@[simp]
theorem initialOnly_isRoot_iff
    (history : base.toArena.HistoryFrom base.init) :
    (initialOnly base).IsRoot history ↔
      history = Arena.HistoryFrom.nil base.toArena base.init :=
  Iff.rfl

@[simp]
theorem allHistories_isRoot
    (history : base.toArena.HistoryFrom base.init) :
    (allHistories base).IsRoot history :=
  trivial

end ContinuationRootPresentation

namespace CompleteInformation

/-- The complete-history carrier used by the canonical complete-information
presentation. -/
abbrev History (base : ExtensiveGame N U) :=
  base.toArena.HistoryFrom base.init

/-- An orthogonal public projection for a history-information presentation.

Private observation and decision information remain the complete history;
this component controls only which public quotient of that history is
exposed. -/
structure PublicObservationPresentation
    (base : ExtensiveGame N U) where
  /-- Public observation carrier. -/
  PublicObservation : Type uP
  /-- Public projection of a complete history. -/
  publicObserve : History base → PublicObservation

namespace PublicObservationPresentation

variable {base : ExtensiveGame N U}

/-- Public-observation presentations are determined by their carrier and
history projection. -/
@[ext]
theorem ext
    (first second : PublicObservationPresentation base)
    (hcarrier :
      first.PublicObservation = second.PublicObservation)
    (hprojection :
      HEq first.publicObserve second.publicObserve) :
    first = second := by
  cases first
  cases second
  cases hcarrier
  cases hprojection
  rfl

/-- Keep the entire complete history public. -/
def fullHistory (base : ExtensiveGame N U) :
    PublicObservationPresentation base where
  PublicObservation := History base
  publicObserve := fun history => history

/-- Hide all history detail from the public observation. -/
def trivial (base : ExtensiveGame N U) :
    PublicObservationPresentation base where
  PublicObservation := Unit
  publicObserve := fun _history => ()

@[simp]
theorem fullHistory_publicObserve
    (base : ExtensiveGame N U) (history : History base) :
    (fullHistory base).publicObserve history = history :=
  rfl

@[simp]
theorem trivial_publicObserve
    (base : ExtensiveGame N U) (history : History base) :
    (trivial base).publicObserve history = () :=
  rfl

end PublicObservationPresentation

/-- Player `i`'s complete-history information state.

This intentionally includes histories where `i` does not move. Consequently
`PureStrategy i` asks for an action at every complete history; callers whose
action family is empty away from `i`'s decision histories should instead use
a decision-history subtype, as the occurrence-sensitive `GameTree` compiler
does. -/
abbrev InfoState (base : ExtensiveGame N U) (_i : N) :=
  History base

/-- Legal actions at a complete decision history. -/
abbrev InfoAction (base : ExtensiveGame N U) (i : N)
    (information : InfoState base i) :=
  base.Action information.1

end CompleteInformation

/-- Equip an ordinary extensive game with complete-history private
observations and information states, plus explicit public and root
presentations.

The public projection is automatically reused as `publicOf`, so the
private/public compatibility proof is definitional. This constructor is the
orthogonal base of `completeInformationPresentation`; it is useful when
players remember the full history but public disclosure is intentionally
coarser. -/
abbrev historyInformationPresentation
    (base : ExtensiveGame N U)
    (publicPresentation :
      CompleteInformation.PublicObservationPresentation base)
    (roots : ContinuationRootPresentation base) :
    ObservedGame N U where
  base := base
  Observation := fun _i => CompleteInformation.History base
  PublicObservation := publicPresentation.PublicObservation
  observe := fun _i history => history
  publicObserve := publicPresentation.publicObserve
  publicOf :=
    fun _i observation => publicPresentation.publicObserve observation
  observe_public := fun _i _history => rfl
  InfoState := CompleteInformation.InfoState base
  infoObserve := fun _i information => information
  infoAt := fun history _i _hmover => history
  infoAt_observe := fun _history _i _hmover => rfl
  InfoAction := CompleteInformation.InfoAction base
  actionEquiv := fun _history _i _hmover => Equiv.refl _
  IsDesignatedContinuationRoot := roots.IsRoot
  init_isDesignatedContinuationRoot := roots.init_isRoot

/-- Equip an ordinary extensive game with its canonical complete-information
presentation and an explicit choice of presentation-designated roots.

Every player and the public observe the complete history. A player's
information state is that complete history, and its abstract action type is
definitionally the underlying `Arena.Action`. The constructor chooses no
chance law, no measurable structure, and no standard-subgame system. Because
strategies quantify over every information state, callers must ensure that
this total history-indexed action family is the intended strategy domain. -/
abbrev completeInformationPresentation
    (base : ExtensiveGame N U)
    (roots : ContinuationRootPresentation base) :
    ObservedGame N U :=
  historyInformationPresentation base
    (CompleteInformation.PublicObservationPresentation.fullHistory base)
    roots

@[simp]
theorem completeInformationPresentation_base
    (base : ExtensiveGame N U)
    (roots : ContinuationRootPresentation base) :
    (completeInformationPresentation base roots).base = base :=
  rfl

@[simp]
theorem completeInformationPresentation_observe
    (base : ExtensiveGame N U)
    (roots : ContinuationRootPresentation base) (i : N)
    (history : base.toArena.HistoryFrom base.init) :
    (completeInformationPresentation base roots).observe i history =
      history :=
  rfl

@[simp]
theorem completeInformationPresentation_publicObserve
    (base : ExtensiveGame N U)
    (roots : ContinuationRootPresentation base)
    (history : base.toArena.HistoryFrom base.init) :
    (completeInformationPresentation base roots).publicObserve history =
      history :=
  rfl

@[simp]
theorem completeInformationPresentation_publicOf
    (base : ExtensiveGame N U)
    (roots : ContinuationRootPresentation base) (i : N)
    (observation :
      (completeInformationPresentation base roots).Observation i) :
    (completeInformationPresentation base roots).publicOf i observation =
      observation :=
  rfl

@[simp]
theorem completeInformationPresentation_infoObserve
    (base : ExtensiveGame N U)
    (roots : ContinuationRootPresentation base) (i : N)
    (information :
      (completeInformationPresentation base roots).InfoState i) :
    (completeInformationPresentation base roots).infoObserve i information =
      information :=
  rfl

@[simp]
theorem completeInformationPresentation_infoAt
    (base : ExtensiveGame N U)
    (roots : ContinuationRootPresentation base)
    (history : base.toArena.HistoryFrom base.init) (i : N)
    (hmover : base.mover history.1 = some i) :
    (completeInformationPresentation base roots).infoAt
        history i hmover =
      history :=
  rfl

@[simp]
theorem completeInformationPresentation_isDesignatedContinuationRoot
    (base : ExtensiveGame N U)
    (roots : ContinuationRootPresentation base)
    (history : base.toArena.HistoryFrom base.init) :
    (completeInformationPresentation base roots).IsDesignatedContinuationRoot
        history ↔
      roots.IsRoot history :=
  Iff.rfl

/-- `current` extends `root` when it is reachable from `root` in the complete
history unfolding.  Because states of the unfolding are complete histories,
this is the occurrence-sensitive prefix relation rather than mere
reachability between compact world states. -/
def IsContinuationOf
    (root current :
      G.base.toArena.HistoryFrom G.base.init) : Prop :=
  Arena.Reachable G.base.unfold.toArena root current

/-- Every history is a continuation of itself. -/
theorem IsContinuationOf.refl
    (root : G.base.toArena.HistoryFrom G.base.init) :
    G.IsContinuationOf root root :=
  by
    change Arena.Reachable G.base.unfold.toArena root root
    exact @Arena.Reachable.refl G.base.unfold.toArena root

/-- The information-set conditions making one history a lawful standard
subgame root.

This predicate is independent of the presentation's designated continuation
roots. The initial history represents the whole game and is lawful by
convention. A proper root must be a singleton decision information set when
controlled by a player, and every information set encountered after entry
must be wholly contained in the continuation. -/
structure IsLawfulSubgameRoot
    (root : G.base.toArena.HistoryFrom G.base.init) : Prop where
  /-- A player decision at a proper root has a singleton information set.
  The initial history is exempt because it represents the whole game. -/
  root_information_singleton :
    root ≠ Arena.HistoryFrom.nil G.base.toArena G.base.init →
      ∀ (i : N) (hmover : G.base.mover root.1 = some i)
      (other : G.base.toArena.HistoryFrom G.base.init)
      (hother : G.base.mover other.1 = some i),
      G.infoAt root i hmover =
          G.infoAt other i hother →
        other = root
  /-- Any player information set met after entering at `root` remains wholly
  inside its continuation. -/
  information_closed :
    ∀ current, G.IsContinuationOf root current →
      ∀ (i : N) (hmover : G.base.mover current.1 = some i)
        (other : G.base.toArena.HistoryFrom G.base.init)
        (hother : G.base.mover other.1 = some i),
        G.infoAt current i hmover =
            G.infoAt other i hother →
          G.IsContinuationOf root other

/-- An explicit system of lawful subgame roots.

The certificate requires `IsLawfulSubgameRoot`: the whole-game initial root is
admitted by convention, every proper player root has singleton decision
information, and every later information set intersecting the continuation is
contained in it. It is deliberately independent of presentation-designated
continuation roots. Presentation visibility is the separate
`SubgameSystem.IsPresentationVisible` property below.

The structure does not claim that every lawful root is selected. Equilibrium
on this possibly conservative system is therefore named
`IsPureSubgamePerfectOn`; a complete standard-subgame claim additionally uses
`CompleteSubgameSystem`. -/
structure SubgameSystem where
  /-- Roots admitted by this explicit lawful subgame convention. -/
  IsRoot :
    G.base.toArena.HistoryFrom G.base.init → Prop
  /-- The whole game is a subgame. -/
  init_isRoot :
    IsRoot (Arena.HistoryFrom.nil G.base.toArena G.base.init)
  /-- Every selected root satisfies the single-root structural lawfulness
  predicate. -/
  lawful :
    ∀ root, IsRoot root → G.IsLawfulSubgameRoot root

namespace SubgameSystem

variable {G : ObservedGame N U}

/-- Every root selected by a `SubgameSystem` satisfies the representation-
independent information-set lawfulness predicate. -/
def isLawful (system : G.SubgameSystem)
    {root : G.base.toArena.HistoryFrom G.base.init}
    (hroot : system.IsRoot root) :
    G.IsLawfulSubgameRoot root :=
  system.lawful root hroot

/-- Whether every root in a lawful system is also exposed by the
presentation's designated-continuation metadata.

This is intentionally a property rather than a field: mathematical subgame
lawfulness and standard SPE do not depend on presentation visibility. -/
def IsPresentationVisible (system : G.SubgameSystem) : Prop :=
  ∀ root, system.IsRoot root → G.IsDesignatedContinuationRoot root

/-- Derived compatibility accessor for the proper-root singleton condition. -/
theorem root_information_singleton (system : G.SubgameSystem)
    (root : G.base.toArena.HistoryFrom G.base.init)
    (hroot : system.IsRoot root)
    (hproper :
      root ≠ Arena.HistoryFrom.nil G.base.toArena G.base.init) :
    ∀ (i : N) (hmover : G.base.mover root.1 = some i)
      (other : G.base.toArena.HistoryFrom G.base.init)
      (hother : G.base.mover other.1 = some i),
      G.infoAt root i hmover =
          G.infoAt other i hother →
        other = root :=
  (system.isLawful hroot).root_information_singleton hproper

/-- Derived compatibility accessor for information-set closure. -/
theorem information_closed (system : G.SubgameSystem)
    (root : G.base.toArena.HistoryFrom G.base.init)
    (hroot : system.IsRoot root) :
    ∀ current, G.IsContinuationOf root current →
      ∀ (i : N) (hmover : G.base.mover current.1 = some i)
        (other : G.base.toArena.HistoryFrom G.base.init)
        (hother : G.base.mover other.1 = some i),
        G.infoAt current i hmover =
            G.infoAt other i hother →
          G.IsContinuationOf root other :=
  (system.isLawful hroot).information_closed

end SubgameSystem

/-- The initial history is always a lawful subgame root: it represents the
whole game, and every complete history lies in its continuation. This remains
true when an imperfect-recall presentation reuses the initial decision
information state later in play. -/
theorem init_isLawfulSubgameRoot (G : ObservedGame N U) :
    G.IsLawfulSubgameRoot
      (Arena.HistoryFrom.nil G.base.toArena G.base.init) where
  root_information_singleton := by
    intro hproper
    exact (hproper rfl).elim
  information_closed := by
    intro _current _hcurrent i _hmover other _hother _hsame
    exact other.2.reachableInUnfolding G.base.toArena G.base.init

/-- The smallest lawful subgame system selects only the whole-game initial
root. This is independent of which additional roots the presentation
designates. -/
def SubgameSystem.initialOnly (G : ObservedGame N U) :
    G.SubgameSystem where
  IsRoot := fun root =>
    root = Arena.HistoryFrom.nil G.base.toArena G.base.init
  init_isRoot := rfl
  lawful := by
    intro root hroot
    subst root
    exact G.init_isLawfulSubgameRoot

@[simp]
theorem SubgameSystem.initialOnly_isRoot_iff
    (G : ObservedGame N U)
    (root : G.base.toArena.HistoryFrom G.base.init) :
    (SubgameSystem.initialOnly G).IsRoot root ↔
      root = Arena.HistoryFrom.nil G.base.toArena G.base.init :=
  Iff.rfl

/-- A complete standard-subgame system.

It extends a lawful system with the converse coverage law: every structurally
lawful root of the observed EFG is selected. Its existence is independent of
presentation-designated continuation metadata. -/
structure CompleteSubgameSystem extends G.SubgameSystem where
  /-- Every structurally lawful subgame root is present in the system. -/
  complete :
    ∀ root, G.IsLawfulSubgameRoot root →
      toSubgameSystem.IsRoot root

namespace CompleteSubgameSystem

variable {G : ObservedGame N U}

/-- A complete system selects exactly the structurally lawful roots. -/
theorem isRoot_iff_isLawful (system : G.CompleteSubgameSystem)
    (root : G.base.toArena.HistoryFrom G.base.init) :
    system.toSubgameSystem.IsRoot root ↔
      G.IsLawfulSubgameRoot root :=
  ⟨system.toSubgameSystem.isLawful, system.complete root⟩

/-- The canonical complete system selects exactly the structurally lawful
roots. It exists for every observed EFG and does not inspect designated-root
metadata. -/
def canonical (G : ObservedGame N U) : G.CompleteSubgameSystem where
  IsRoot := G.IsLawfulSubgameRoot
  init_isRoot := G.init_isLawfulSubgameRoot
  lawful := fun _root hroot => hroot
  complete := fun _root hroot => hroot

end CompleteSubgameSystem

/-- A game-bound pure strategy for player `i`: one abstract action at every
information state, with no concrete history argument. -/
def PureStrategy (i : N) : Type _ :=
  (I : G.InfoState i) → G.InfoAction i I

/-- A pure-strategy profile for all players. -/
def PureProfile : Type _ :=
  (i : N) → G.PureStrategy i

/-- The legal base action prescribed by a pure strategy at a concrete history
controlled by player `i`. -/
def PureStrategy.actionAt {i : N} (σ : G.PureStrategy i)
    (h : G.base.toArena.HistoryFrom G.base.init)
    (hmover : G.base.mover h.1 = some i) :
    G.base.Action h.1 :=
  G.actionEquiv h i hmover (σ (G.infoAt h i hmover))

/-- The legal base action prescribed by a profile at a concrete
player-controlled history. -/
def PureProfile.actionAt (σ : G.PureProfile)
    (h : G.base.toArena.HistoryFrom G.base.init) (i : N)
    (hmover : G.base.mover h.1 = some i) :
    G.base.Action h.1 :=
  (σ i).actionAt G h hmover

/-- Equal information states force a pure profile to make the same packaged
abstract choice.  Packaging the action with its dependent information-state
index states constancy without choosing a transport between action types. -/
theorem PureProfile.choice_eq_of_infoState_eq
    (σ : G.PureProfile) (i : N)
    (h k : G.base.toArena.HistoryFrom G.base.init)
    (hmover : G.base.mover h.1 = some i)
    (kmover : G.base.mover k.1 = some i)
    (hsame : G.infoAt h i hmover = G.infoAt k i kmover) :
    (⟨G.infoAt h i hmover, σ i (G.infoAt h i hmover)⟩ :
      Σ I : G.InfoState i, G.InfoAction i I) =
    ⟨G.infoAt k i kmover, σ i (G.infoAt k i kmover)⟩ :=
  congrArg
    (fun I : G.InfoState i =>
      (⟨I, σ i I⟩ : Σ J : G.InfoState i, G.InfoAction i J))
    hsame

/-- Equal decision information states imply equal public observations at the
represented histories. -/
theorem publicObserve_eq_of_infoAt_eq
    (i : N) (h k : G.base.toArena.HistoryFrom G.base.init)
    (hmover : G.base.mover h.1 = some i)
    (kmover : G.base.mover k.1 = some i)
    (hsame : G.infoAt h i hmover = G.infoAt k i kmover) :
    G.publicObserve h = G.publicObserve k := by
  calc
    G.publicObserve h = G.publicOf i (G.observe i h) :=
      (G.observe_public i h).symm
    _ = G.publicOf i (G.infoObserve i (G.infoAt h i hmover)) := by
      rw [G.infoAt_observe h i hmover]
    _ = G.publicOf i (G.infoObserve i (G.infoAt k i kmover)) := by
      rw [hsame]
    _ = G.publicOf i (G.observe i k) := by
      rw [G.infoAt_observe k i kmover]
    _ = G.publicObserve k := G.observe_public i k

/-- The mover option at a nonterminal history is inhabited in a no-chance
game. -/
def moverIsSome (hNoChance : G.base.NoChance)
    (h : G.base.toArena.HistoryFrom G.base.init)
    (hnonterminal : ¬ G.base.isTerminal h.1) :
    (G.base.mover h.1).isSome = true :=
  Option.isSome_iff_exists.mpr (hNoChance h.1 hnonterminal)

/-- The strategic player controlling a nonterminal history in a no-chance
game. -/
def playerAt (hNoChance : G.base.NoChance)
    (h : G.base.toArena.HistoryFrom G.base.init)
    (hnonterminal : ¬ G.base.isTerminal h.1) : N :=
  (G.base.mover h.1).get (G.moverIsSome hNoChance h hnonterminal)

/-- `playerAt` recovers the player stored in the base mover field. -/
theorem mover_playerAt (hNoChance : G.base.NoChance)
    (h : G.base.toArena.HistoryFrom G.base.init)
    (hnonterminal : ¬ G.base.isTerminal h.1) :
    G.base.mover h.1 =
      some (G.playerAt hNoChance h hnonterminal) :=
  (Option.some_get (G.moverIsSome hNoChance h hnonterminal)).symm

/-- Convert a pure profile into a terminal-aware history policy when the base
game has no chance nodes. -/
def PureProfile.toHistoryPolicy (σ : G.PureProfile)
    (hNoChance : G.base.NoChance) :
    G.base.toArena.HistoryPolicy G.base.init :=
  fun h hnonterminal =>
    σ.actionAt G h (G.playerAt hNoChance h hnonterminal)
      (G.mover_playerAt hNoChance h hnonterminal)

/-- At a player-controlled history, profile execution uses exactly
`PureProfile.actionAt`. -/
theorem PureProfile.toHistoryPolicy_of_mover
    (σ : G.PureProfile) (hNoChance : G.base.NoChance)
    (h : G.base.toArena.HistoryFrom G.base.init)
    (hnonterminal : ¬ G.base.isTerminal h.1) (i : N)
    (hmover : G.base.mover h.1 = some i) :
    σ.toHistoryPolicy G hNoChance h hnonterminal =
      σ.actionAt G h i hmover := by
  have hplayer : G.playerAt hNoChance h hnonterminal = i := by
    apply Option.some.inj
    rw [← hmover]
    exact (G.mover_playerAt hNoChance h hnonterminal).symm
  subst i
  rfl

/-- Continue executing a no-chance pure profile from an accumulated history,
stopping at a terminal endpoint or when `fuel` is exhausted. -/
def stoppedHistoryFrom
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (σ : G.PureProfile) (hNoChance : G.base.NoChance)
    (current : G.base.toArena.HistoryFrom G.base.init) (fuel : ℕ) :
    G.base.toArena.HistoryFrom G.base.init :=
  G.base.toArena.stoppedHistoryFrom
    (σ.toHistoryPolicy G hNoChance) current fuel

/-- Return the terminal payoff reached by continuing a no-chance pure profile
from an accumulated history, or `none` when the supplied fuel expires first. -/
def stoppedPayoffFrom
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (σ : G.PureProfile) (hNoChance : G.base.NoChance)
    (current : G.base.toArena.HistoryFrom G.base.init) (fuel : ℕ) :
    Option (N → U) :=
  let result := G.stoppedHistoryFrom σ hNoChance current fuel
  if G.base.isTerminal result.1 then
    some (G.base.payoff result.1)
  else
    none

/-- Execute a no-chance pure profile from the initial empty history, stopping
at a terminal endpoint or when `fuel` is exhausted. -/
def stoppedHistory
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (σ : G.PureProfile) (hNoChance : G.base.NoChance) (fuel : ℕ) :
    G.base.toArena.HistoryFrom G.base.init :=
  G.stoppedHistoryFrom σ hNoChance
    (Arena.HistoryFrom.nil G.base.toArena G.base.init) fuel

/-- Return the terminal payoff reached by a no-chance pure profile, or `none`
if its execution exhausts the supplied fuel first. -/
def stoppedPayoff
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (σ : G.PureProfile) (hNoChance : G.base.NoChance) (fuel : ℕ) :
    Option (N → U) :=
  G.stoppedPayoffFrom σ hNoChance
    (Arena.HistoryFrom.nil G.base.toArena G.base.init) fuel

end ObservedGame

end ExtensiveGame
