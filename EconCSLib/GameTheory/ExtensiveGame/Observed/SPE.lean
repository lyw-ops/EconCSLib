/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Operational

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.SPE

Termination-certified total continuation semantics and pure
subgame-perfect equilibrium for history-indexed observed extensive games.

The general Arena model permits infinite play, so a total terminal payoff
cannot be extracted without an explicit termination assumption. The local
primitive is termination of every pure profile from one accumulated history:

```lean
G.PureTerminatingAt hNoChance current
```

`PureTerminating` quantifies that condition over every
presentation-designated continuation root, while `PureTerminatingOn`
restricts it to an explicit lawful subgame system. Both relative-system and
standard SPE use `PureTerminatingOn`; standard SPE additionally requires a
`CompleteSubgameSystem`, certifying that every structurally lawful root is
selected independently of designated-root metadata. The bound may depend on
the root and profile.
`Arena.stoppedHistoryFrom_eq_of_terminal` proves that any two bounds which have
already terminated produce the same history; consequently the chosen terminal
payoff is independent of the witness fuel.

A strict `ObservedGame.Iso` transports termination, total continuation game
forms, relative-system pure SPE, and complete standard pure SPE in both
directions.

## Main definitions

* `ObservedGame.PureTerminatesFrom` — one profile eventually terminates from
  one accumulated history.
* `ObservedGame.PureTerminating` — all pure profiles terminate from every
  presentation-designated continuation root.
* `ObservedGame.terminalContinuationGameForm` — total `N → U` continuation
  outcome semantics.
* `ObservedGame.IsPureNashOnDesignatedContinuations` — Nash equilibrium at
  every presentation-designated continuation root.
* `ObservedGame.IsPureSubgamePerfectOn` — pure subgame perfection on an
  explicit, possibly conservative lawful `SubgameSystem`.
* `ObservedGame.IsPureStandardSubgamePerfect` — standard SPE on a
  `CompleteSubgameSystem` containing every structurally lawful root.

## Main results

* `Iso.pureTerminatesFrom_iff` and `pureTerminating_iff` — termination
  invariance.
* `Iso.map_terminalHistoryFrom` and `map_terminalPayoffFrom` — exact total
  outcome preservation.
* `Iso.isPureSubgamePerfectOn_iff` — relative-system pure-SPE transfer in both
  directions.
* `Iso.isPureStandardSubgamePerfect_iff` — complete standard-SPE transfer in
  both directions.
-/

namespace ExtensiveGame.ObservedGame

universe uV

variable {N U : Type*}

/-- A pure profile eventually reaches a terminal history from `current`. -/
def PureTerminatesFrom
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (profile : G.PureProfile)
    (hNoChance : G.base.NoChance)
    (current : G.base.toArena.HistoryFrom G.base.init) : Prop :=
  ∃ fuel : ℕ,
    G.base.isTerminal
      (G.stoppedHistoryFrom profile hNoChance current fuel).1

/-- Every pure profile terminates from one accumulated history. -/
def PureTerminatingAt
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChance)
    (current : G.base.toArena.HistoryFrom G.base.init) : Prop :=
  ∀ profile : G.PureProfile,
    G.PureTerminatesFrom profile hNoChance current

/-- Every pure profile terminates from every presentation-designated
continuation root. -/
def PureTerminating
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChance) : Prop :=
  ∀ current : G.base.toArena.HistoryFrom G.base.init,
    G.IsDesignatedContinuationRoot current →
      G.PureTerminatingAt hNoChance current

/-- Every pure profile terminates from each root of one explicit lawful
subgame system. -/
def PureTerminatingOn
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChance)
    (system : G.SubgameSystem) : Prop :=
  ∀ current : G.base.toArena.HistoryFrom G.base.init,
    system.IsRoot current →
      G.PureTerminatingAt hNoChance current

/-- Termination on all presentation-designated continuations implies
termination on a lawful subgame system when that system is separately proved
presentation-visible. -/
theorem PureTerminating.onSubgameSystem
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChance)
    (hterminates : G.PureTerminating hNoChance)
    (system : G.SubgameSystem)
    (hvisible : system.IsPresentationVisible) :
    G.PureTerminatingOn hNoChance system :=
  fun current hroot =>
    hterminates current (hvisible current hroot)

/-- A witness fuel at which an eventually terminating pure continuation has
reached a terminal history. -/
noncomputable def terminalFuel
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (profile : G.PureProfile)
    (hNoChance : G.base.NoChance)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (hterminates : G.PureTerminatesFrom profile hNoChance current) : ℕ :=
  hterminates.choose

/-- The selected termination fuel really reaches a terminal history. -/
theorem terminalFuel_spec
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (profile : G.PureProfile)
    (hNoChance : G.base.NoChance)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (hterminates : G.PureTerminatesFrom profile hNoChance current) :
    G.base.isTerminal
      (G.stoppedHistoryFrom profile hNoChance current
        (G.terminalFuel profile hNoChance current hterminates)).1 :=
  hterminates.choose_spec

/-- The terminal history selected from an existential pure-termination
witness. -/
noncomputable def terminalHistoryFrom
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (profile : G.PureProfile)
    (hNoChance : G.base.NoChance)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (hterminates : G.PureTerminatesFrom profile hNoChance current) :
    G.base.toArena.HistoryFrom G.base.init :=
  G.stoppedHistoryFrom profile hNoChance current
    (G.terminalFuel profile hNoChance current hterminates)

/-- The selected eventual history is terminal. -/
theorem terminalHistoryFrom_terminal
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (profile : G.PureProfile)
    (hNoChance : G.base.NoChance)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (hterminates : G.PureTerminatesFrom profile hNoChance current) :
    G.base.isTerminal
      (G.terminalHistoryFrom profile hNoChance current hterminates).1 :=
  G.terminalFuel_spec profile hNoChance current hterminates

/-- The selected terminal history equals the result at any other fuel which
has already reached a terminal endpoint. -/
theorem terminalHistoryFrom_eq_of_terminal
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (profile : G.PureProfile)
    (hNoChance : G.base.NoChance)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (hterminates : G.PureTerminatesFrom profile hNoChance current)
    (fuel : ℕ)
    (hterminal :
      G.base.isTerminal
        (G.stoppedHistoryFrom profile hNoChance current fuel).1) :
    G.terminalHistoryFrom profile hNoChance current hterminates =
      G.stoppedHistoryFrom profile hNoChance current fuel := by
  exact
    Arena.stoppedHistoryFrom_eq_of_terminal
      (profile.toHistoryPolicy G hNoChance) current
      (G.terminalFuel profile hNoChance current hterminates) fuel
      (G.terminalHistoryFrom_terminal
        profile hNoChance current hterminates)
      hterminal

/-- The total terminal payoff of an eventually terminating pure
continuation. -/
noncomputable def terminalPayoffFrom
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (profile : G.PureProfile)
    (hNoChance : G.base.NoChance)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (hterminates : G.PureTerminatesFrom profile hNoChance current) :
    N → U :=
  G.base.payoff
    (G.terminalHistoryFrom profile hNoChance current hterminates).1

namespace Iso

variable {G H : ObservedGame N U}

/-- Transport the structural lawfulness of one target root from its inverse
image through a strict observed-EFG isomorphism. -/
def mapLawfulSubgameRoot
    (e : G.Iso H)
    (root : H.base.toArena.HistoryFrom H.base.init)
    (hlawful :
      G.IsLawfulSubgameRoot
        (e.historyIso.stateEquiv.symm root)) :
    H.IsLawfulSubgameRoot root where
  root_information_singleton := by
    intro hproper i hmover other hother hinfo
    let f := e.symm
    have hsourceProper :
        f.historyIso.stateEquiv root ≠
          Arena.HistoryFrom.nil G.base.toArena G.base.init := by
      intro hsourceInit
      apply hproper
      apply f.historyIso.stateEquiv.injective
      exact hsourceInit.trans f.map_init.symm
    have hrootMover :
        G.base.mover (f.historyIso.stateEquiv root).1 = some i := by
      rw [f.map_mover root, hmover]
    have hotherMover :
        G.base.mover (f.historyIso.stateEquiv other).1 = some i := by
      rw [f.map_mover other, hother]
    have hsourceInfo :
        G.infoAt (f.historyIso.stateEquiv root) i hrootMover =
          G.infoAt (f.historyIso.stateEquiv other) i hotherMover := by
      rw [← f.map_infoAt root i hmover hrootMover,
        ← f.map_infoAt other i hother hotherMover, hinfo]
    have hsourceEq :=
      hlawful.root_information_singleton
        hsourceProper
        i hrootMover
        (f.historyIso.stateEquiv other) hotherMover
        hsourceInfo
    exact f.historyIso.stateEquiv.injective hsourceEq
  information_closed := by
    intro current hcurrent i hmover other hother hinfo
    let f := e.symm
    have hcurrentSource :
        G.IsContinuationOf
          (f.historyIso.stateEquiv root)
          (f.historyIso.stateEquiv current) :=
      (f.map_isContinuationOf root current).mp hcurrent
    have hcurrentMover :
        G.base.mover (f.historyIso.stateEquiv current).1 = some i := by
      rw [f.map_mover current, hmover]
    have hotherMover :
        G.base.mover (f.historyIso.stateEquiv other).1 = some i := by
      rw [f.map_mover other, hother]
    have hsourceInfo :
        G.infoAt (f.historyIso.stateEquiv current) i hcurrentMover =
          G.infoAt (f.historyIso.stateEquiv other) i hotherMover := by
      rw [← f.map_infoAt current i hmover hcurrentMover,
        ← f.map_infoAt other i hother hotherMover, hinfo]
    have hotherSource :=
      hlawful.information_closed
        (f.historyIso.stateEquiv current) hcurrentSource
        i hcurrentMover
        (f.historyIso.stateEquiv other) hotherMover
        hsourceInfo
    exact (f.map_isContinuationOf root other).mpr hotherSource

/-- Transport a lawful standard-subgame system through a strict observed-EFG
isomorphism.  Roots are pulled back along the history equivalence, while the
singleton and information-set closure laws are transported through the
information-state and continuation equivalences. -/
def mapSubgameSystem
    (e : G.Iso H) (system : G.SubgameSystem) :
    H.SubgameSystem where
  IsRoot target :=
    system.IsRoot (e.historyIso.stateEquiv.symm target)
  init_isRoot := by
    rw [← e.map_init, Equiv.symm_apply_apply]
    exact system.init_isRoot
  lawful := by
    intro target hroot
    exact e.mapLawfulSubgameRoot target (system.isLawful hroot)

/-- Transport a complete standard-subgame system through a strict
observed-EFG isomorphism. Completeness is preserved because structural
lawfulness is reflected by the inverse isomorphism. -/
def mapCompleteSubgameSystem
    (e : G.Iso H) (system : G.CompleteSubgameSystem) :
    H.CompleteSubgameSystem where
  toSubgameSystem :=
    e.mapSubgameSystem system.toSubgameSystem
  complete := by
    intro target htarget
    let source :=
      e.historyIso.stateEquiv.symm target
    have hsource : G.IsLawfulSubgameRoot source := by
      apply e.symm.mapLawfulSubgameRoot source
      change
        H.IsLawfulSubgameRoot
          (e.historyIso.stateEquiv source)
      rw [show e.historyIso.stateEquiv source = target by
        exact e.historyIso.stateEquiv.apply_symm_apply target]
      exact htarget
    exact system.complete source hsource

/-- Eventual pure termination at corresponding histories is invariant under a
strict observed-EFG isomorphism. -/
theorem pureTerminatesFrom_iff
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (profile : G.PureProfile)
    (hNoChanceG : G.base.NoChance)
    (hNoChanceH : H.base.NoChance)
    (current : G.base.toArena.HistoryFrom G.base.init) :
    G.PureTerminatesFrom profile hNoChanceG current ↔
      H.PureTerminatesFrom (e.mapProfile profile) hNoChanceH
        (e.historyIso.stateEquiv current) := by
  constructor
  · rintro ⟨fuel, hterminal⟩
    refine ⟨fuel, ?_⟩
    rw [← e.map_stoppedHistoryFrom
      profile hNoChanceG hNoChanceH current fuel]
    exact
      (e.isTerminal_iff
        (G.stoppedHistoryFrom profile hNoChanceG current fuel)).mp
        hterminal
  · rintro ⟨fuel, hterminal⟩
    refine ⟨fuel, ?_⟩
    have hmapped :
        H.base.isTerminal
          (e.historyIso.stateEquiv
            (G.stoppedHistoryFrom profile hNoChanceG current fuel)).1 := by
      rw [e.map_stoppedHistoryFrom
        profile hNoChanceG hNoChanceH current fuel]
      exact hterminal
    exact
      (e.isTerminal_iff
        (G.stoppedHistoryFrom profile hNoChanceG current fuel)).mpr
        hmapped

/-- Map a global pure-termination certificate through a strict observed-EFG
isomorphism. -/
theorem map_pureTerminating
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (hNoChanceG : G.base.NoChance)
    (hNoChanceH : H.base.NoChance)
    (hterminates : G.PureTerminating hNoChanceG) :
    H.PureTerminating hNoChanceH := by
  intro targetRoot htargetRoot targetProfile
  let sourceRoot := e.historyIso.stateEquiv.symm targetRoot
  let sourceProfile := e.unmapProfile targetProfile
  have hmapRoot :
      e.historyIso.stateEquiv sourceRoot = targetRoot :=
    e.historyIso.stateEquiv.apply_symm_apply targetRoot
  have hsourceRoot : G.IsDesignatedContinuationRoot sourceRoot := by
    apply (e.map_designatedContinuationRoot sourceRoot).mpr
    simpa [hmapRoot] using htargetRoot
  have hsourceTerminates :=
    hterminates sourceRoot hsourceRoot sourceProfile
  have hmapped :=
    (e.pureTerminatesFrom_iff sourceProfile
      hNoChanceG hNoChanceH sourceRoot).mp hsourceTerminates
  simpa [sourceProfile, hmapRoot] using hmapped

/-- Map a pure-termination certificate on one lawful subgame system through a
strict observed-EFG isomorphism. -/
theorem map_pureTerminatingOn
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (hNoChanceG : G.base.NoChance)
    (hNoChanceH : H.base.NoChance)
    (system : G.SubgameSystem)
    (hterminates : G.PureTerminatingOn hNoChanceG system) :
    H.PureTerminatingOn hNoChanceH (e.mapSubgameSystem system) := by
  intro targetRoot htargetRoot targetProfile
  let sourceRoot := e.historyIso.stateEquiv.symm targetRoot
  let sourceProfile := e.unmapProfile targetProfile
  have hmapRoot :
      e.historyIso.stateEquiv sourceRoot = targetRoot :=
    e.historyIso.stateEquiv.apply_symm_apply targetRoot
  have hsourceTerminates :=
    hterminates sourceRoot htargetRoot sourceProfile
  have hmapped :=
    (e.pureTerminatesFrom_iff sourceProfile
      hNoChanceG hNoChanceH sourceRoot).mp hsourceTerminates
  simpa [sourceProfile, hmapRoot] using hmapped

/-- Pure termination at every admissible root is invariant under strict
observed-EFG isomorphism. -/
theorem pureTerminating_iff
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (hNoChanceG : G.base.NoChance)
    (hNoChanceH : H.base.NoChance) :
    G.PureTerminating hNoChanceG ↔
      H.PureTerminating hNoChanceH := by
  constructor
  · exact e.map_pureTerminating hNoChanceG hNoChanceH
  · intro hterminates sourceRoot hsourceRoot sourceProfile
    have htargetRoot :
        H.IsDesignatedContinuationRoot (e.historyIso.stateEquiv sourceRoot) :=
      (e.map_designatedContinuationRoot sourceRoot).mp hsourceRoot
    have htargetTerminates :=
      hterminates (e.historyIso.stateEquiv sourceRoot) htargetRoot
        (e.mapProfile sourceProfile)
    exact
      (e.pureTerminatesFrom_iff sourceProfile
        hNoChanceG hNoChanceH sourceRoot).mpr htargetTerminates

/-- Strict history mapping sends the selected source terminal history to the
selected target terminal history.  Although the two existential certificates
may choose different fuel values, terminal-run uniqueness identifies their
results. -/
theorem map_terminalHistoryFrom
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (profile : G.PureProfile)
    (hNoChanceG : G.base.NoChance)
    (hNoChanceH : H.base.NoChance)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (hterminatesG :
      G.PureTerminatesFrom profile hNoChanceG current)
    (hterminatesH :
      H.PureTerminatesFrom (e.mapProfile profile) hNoChanceH
        (e.historyIso.stateEquiv current)) :
    e.historyIso.stateEquiv
        (G.terminalHistoryFrom profile hNoChanceG current hterminatesG) =
      H.terminalHistoryFrom (e.mapProfile profile) hNoChanceH
        (e.historyIso.stateEquiv current) hterminatesH := by
  let sourceFuel :=
    G.terminalFuel profile hNoChanceG current hterminatesG
  have hsourceTerminal :
      G.base.isTerminal
        (G.stoppedHistoryFrom profile hNoChanceG current sourceFuel).1 :=
    G.terminalFuel_spec profile hNoChanceG current hterminatesG
  have hmappedTerminal :
      H.base.isTerminal
        (H.stoppedHistoryFrom (e.mapProfile profile) hNoChanceH
          (e.historyIso.stateEquiv current) sourceFuel).1 := by
    rw [← e.map_stoppedHistoryFrom
      profile hNoChanceG hNoChanceH current sourceFuel]
    exact
      (e.isTerminal_iff
        (G.stoppedHistoryFrom profile hNoChanceG current sourceFuel)).mp
        hsourceTerminal
  calc
    e.historyIso.stateEquiv
        (G.terminalHistoryFrom profile hNoChanceG current hterminatesG) =
        H.stoppedHistoryFrom (e.mapProfile profile) hNoChanceH
          (e.historyIso.stateEquiv current) sourceFuel := by
      exact e.map_stoppedHistoryFrom
        profile hNoChanceG hNoChanceH current sourceFuel
    _ = H.terminalHistoryFrom (e.mapProfile profile) hNoChanceH
          (e.historyIso.stateEquiv current) hterminatesH :=
      (H.terminalHistoryFrom_eq_of_terminal
        (e.mapProfile profile) hNoChanceH
        (e.historyIso.stateEquiv current) hterminatesH
        sourceFuel hmappedTerminal).symm

/-- Strict observed-EFG isomorphisms preserve total eventual terminal payoffs
exactly. -/
theorem map_terminalPayoffFrom
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (profile : G.PureProfile)
    (hNoChanceG : G.base.NoChance)
    (hNoChanceH : H.base.NoChance)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (hterminatesG :
      G.PureTerminatesFrom profile hNoChanceG current)
    (hterminatesH :
      H.PureTerminatesFrom (e.mapProfile profile) hNoChanceH
        (e.historyIso.stateEquiv current)) :
    H.terminalPayoffFrom (e.mapProfile profile) hNoChanceH
        (e.historyIso.stateEquiv current) hterminatesH =
      G.terminalPayoffFrom profile hNoChanceG current hterminatesG := by
  rw [terminalPayoffFrom, terminalPayoffFrom,
    ← e.map_terminalHistoryFrom profile hNoChanceG hNoChanceH
      current hterminatesG hterminatesH]
  exact
    e.map_payoff
      (G.terminalHistoryFrom profile hNoChanceG current hterminatesG)
      (G.terminalHistoryFrom_terminal
        profile hNoChanceG current hterminatesG)

end Iso

/-! ### Total continuation game forms and pure equilibrium layers -/

/-- Total deterministic continuation semantics at an accumulated history,
given termination of every pure profile from that history. -/
noncomputable def terminalContinuationGameForm
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChance)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (hterminates : G.PureTerminatingAt hNoChance current) :
    GameForm N where
  Strategy := G.PureStrategy
  Outcome := N → U
  outcome profile :=
    G.terminalPayoffFrom profile hNoChance current
      (hterminates profile)

/-- Pure Nash equilibrium on every presentation-designated continuation under
total terminal-outcome semantics.

This is the accurate name for the historical predicate that quantified
`ObservedGame.IsDesignatedContinuationRoot` directly.  It is useful for conservative
continuation systems, but is not by itself standard subgame perfection. -/
noncomputable def IsPureNashOnDesignatedContinuations
    {V : Type uV} [DecidableEq N] [Preorder V]
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChance)
    (hterminates : G.PureTerminating hNoChance)
    (utility : (N → U) → N → V)
    (profile : G.PureProfile) : Prop :=
  ∀ current : G.base.toArena.HistoryFrom G.base.init,
    ∀ hroot : G.IsDesignatedContinuationRoot current,
      (G.terminalContinuationGameForm hNoChance current
        (hterminates current hroot)).IsNash utility profile

/-- Pure subgame perfection on an explicit lawful subgame system under total
terminal-outcome semantics.

Unlike the designated-continuation predicate, the roots here carry the
information-set singleton and closure laws in `SubgameSystem`. The supplied
system may still be a conservative subset of all lawful roots, which is why
the primary name ends in `On`. -/
noncomputable def IsPureSubgamePerfectOn
    {V : Type uV} [DecidableEq N] [Preorder V]
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChance)
    (system : G.SubgameSystem)
    (hterminates : G.PureTerminatingOn hNoChance system)
    (utility : (N → U) → N → V)
    (profile : G.PureProfile) : Prop :=
  ∀ current : G.base.toArena.HistoryFrom G.base.init,
    ∀ hroot : system.IsRoot current,
      (G.terminalContinuationGameForm hNoChance current
        (hterminates current hroot)).IsNash utility profile

/-- Standard pure subgame-perfect equilibrium on every structurally lawful
subgame root.

The completeness field rules out a conservative root subset: every root
satisfying `IsLawfulSubgameRoot` is tested. -/
noncomputable def IsPureStandardSubgamePerfect
    {V : Type uV} [DecidableEq N] [Preorder V]
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChance)
    (system : G.CompleteSubgameSystem)
    (hterminates :
      G.PureTerminatingOn hNoChance system.toSubgameSystem)
    (utility : (N → U) → N → V)
    (profile : G.PureProfile) : Prop :=
  G.IsPureSubgamePerfectOn hNoChance system.toSubgameSystem
    hterminates utility profile

/-- Subgame perfection on any lawful system is Nash at that system's initial
root. -/
theorem IsPureSubgamePerfectOn.isNashAtInit
    {V : Type uV} [DecidableEq N] [Preorder V]
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChance)
    (system : G.SubgameSystem)
    (hterminates : G.PureTerminatingOn hNoChance system)
    (utility : (N → U) → N → V)
    (profile : G.PureProfile)
    (hspe :
      G.IsPureSubgamePerfectOn hNoChance system hterminates
        utility profile) :
    (G.terminalContinuationGameForm hNoChance
      (Arena.HistoryFrom.nil G.base.toArena G.base.init)
      (hterminates
        (Arena.HistoryFrom.nil G.base.toArena G.base.init)
        system.init_isRoot)).IsNash utility profile :=
  hspe
    (Arena.HistoryFrom.nil G.base.toArena G.base.init)
    system.init_isRoot

/-- Subgame perfection on a lawful system implies Nash optimality on every
root selected by that same system. -/
theorem IsPureSubgamePerfectOn.toNashOnSystemRoots
    {V : Type uV} [DecidableEq N] [Preorder V]
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChance)
    (system : G.SubgameSystem)
    (hterminates : G.PureTerminatingOn hNoChance system)
    (utility : (N → U) → N → V)
    (profile : G.PureProfile)
    (hspe :
      G.IsPureSubgamePerfectOn hNoChance system
        hterminates
        utility profile) :
    ∀ current, ∀ hroot : system.IsRoot current,
      (G.terminalContinuationGameForm hNoChance current
        (hterminates current hroot)).IsNash
        utility profile := by
  intro current hroot
  exact hspe current hroot

/-- Complete standard SPE is Nash at the initial whole-game root. -/
theorem IsPureStandardSubgamePerfect.isNashAtInit
    {V : Type uV} [DecidableEq N] [Preorder V]
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChance)
    (system : G.CompleteSubgameSystem)
    (hterminates :
      G.PureTerminatingOn hNoChance system.toSubgameSystem)
    (utility : (N → U) → N → V)
    (profile : G.PureProfile)
    (hspe :
      G.IsPureStandardSubgamePerfect hNoChance system
        hterminates utility profile) :
    (G.terminalContinuationGameForm hNoChance
      (Arena.HistoryFrom.nil G.base.toArena G.base.init)
      (hterminates
        (Arena.HistoryFrom.nil G.base.toArena G.base.init)
        system.toSubgameSystem.init_isRoot)).IsNash utility profile :=
  IsPureSubgamePerfectOn.isNashAtInit
    G hNoChance system.toSubgameSystem hterminates
    utility profile hspe

/-- Complete standard SPE is Nash at every structurally lawful subgame root. -/
theorem IsPureStandardSubgamePerfect.toNashOnLawfulRoots
    {V : Type uV} [DecidableEq N] [Preorder V]
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChance)
    (system : G.CompleteSubgameSystem)
    (hterminates :
      G.PureTerminatingOn hNoChance system.toSubgameSystem)
    (utility : (N → U) → N → V)
    (profile : G.PureProfile)
    (hspe :
      G.IsPureStandardSubgamePerfect hNoChance system
        hterminates utility profile) :
    ∀ current, ∀ hlawful : G.IsLawfulSubgameRoot current,
      (G.terminalContinuationGameForm hNoChance current
        (hterminates current
          (system.complete current hlawful))).IsNash
        utility profile := by
  intro current hlawful
  exact hspe current (system.complete current hlawful)

/-- A complete standard SPE is, definitionally, subgame-perfect on its
underlying complete lawful system. -/
theorem IsPureStandardSubgamePerfect.toSubgamePerfectOn
    {V : Type uV} [DecidableEq N] [Preorder V]
    (G : ObservedGame N U)
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    (hNoChance : G.base.NoChance)
    (system : G.CompleteSubgameSystem)
    (hterminates :
      G.PureTerminatingOn hNoChance system.toSubgameSystem)
    (utility : (N → U) → N → V)
    (profile : G.PureProfile)
    (hspe :
      G.IsPureStandardSubgamePerfect hNoChance system
        hterminates utility profile) :
    G.IsPureSubgamePerfectOn hNoChance system.toSubgameSystem
      hterminates utility profile :=
  hspe

namespace Iso

variable {G H : ObservedGame N U}

/-- A strict observed-EFG isomorphism induces a strict game-form isomorphism
between corresponding total continuation games. -/
noncomputable def terminalContinuationGameFormIso
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (hNoChanceG : G.base.NoChance)
    (hNoChanceH : H.base.NoChance)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (hterminatesG : G.PureTerminatingAt hNoChanceG current)
    (hterminatesH :
      H.PureTerminatingAt hNoChanceH
        (e.historyIso.stateEquiv current)) :
    (G.terminalContinuationGameForm
      hNoChanceG current hterminatesG).Iso
      (H.terminalContinuationGameForm hNoChanceH
        (e.historyIso.stateEquiv current) hterminatesH) where
  strategyEquiv := e.strategyEquiv
  outcomeEquiv := Equiv.refl _
  map_outcome := by
    intro profile
    exact
      (e.map_terminalPayoffFrom profile hNoChanceG hNoChanceH current
        (hterminatesG profile)
        (hterminatesH (e.mapProfile profile))).symm

/-- Total continuation game-form isomorphism preserves a shared
outcome-utility interpretation. -/
theorem terminalContinuationGameFormIso_utilityCompatible
    {V : Type uV}
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (hNoChanceG : G.base.NoChance)
    (hNoChanceH : H.base.NoChance)
    (utility : (N → U) → N → V)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (hterminatesG : G.PureTerminatingAt hNoChanceG current)
    (hterminatesH :
      H.PureTerminatingAt hNoChanceH
        (e.historyIso.stateEquiv current)) :
    GameForm.Iso.UtilityCompatible
      (e.terminalContinuationGameFormIso hNoChanceG hNoChanceH current
        hterminatesG hterminatesH)
      utility utility := by
  intro outcome i
  rfl

/-- Strict structural observed-EFG isomorphism preserves total pure-strategy
Nash equilibrium on every presentation-designated continuation in both
directions. -/
theorem isPureNashOnDesignatedContinuations_iff
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (hNoChanceG : G.base.NoChance)
    (hNoChanceH : H.base.NoChance)
    (hterminatesG : G.PureTerminating hNoChanceG)
    (utility : (N → U) → N → V)
    (profile : G.PureProfile) :
    G.IsPureNashOnDesignatedContinuations
        hNoChanceG hterminatesG utility profile ↔
      H.IsPureNashOnDesignatedContinuations hNoChanceH
        (e.map_pureTerminating hNoChanceG hNoChanceH hterminatesG)
        utility (e.mapProfile profile) := by
  let hterminatesH :=
    e.map_pureTerminating hNoChanceG hNoChanceH hterminatesG
  constructor
  · intro hspe targetRoot htargetRoot
    obtain ⟨sourceRoot, rfl⟩ :=
      e.historyIso.stateEquiv.surjective targetRoot
    have hsourceRoot : G.IsDesignatedContinuationRoot sourceRoot :=
      (e.map_designatedContinuationRoot sourceRoot).mpr htargetRoot
    have hsourceNash := hspe sourceRoot hsourceRoot
    have hmapped :=
      GameForm.Iso.isNash_iff
        (e.terminalContinuationGameFormIso
          hNoChanceG hNoChanceH sourceRoot
          (hterminatesG sourceRoot hsourceRoot)
          (hterminatesH
            (e.historyIso.stateEquiv sourceRoot)
            ((e.map_designatedContinuationRoot sourceRoot).mp hsourceRoot)))
        (e.terminalContinuationGameFormIso_utilityCompatible
          hNoChanceG hNoChanceH utility sourceRoot
          (hterminatesG sourceRoot hsourceRoot)
          (hterminatesH
            (e.historyIso.stateEquiv sourceRoot)
            ((e.map_designatedContinuationRoot sourceRoot).mp hsourceRoot)))
        profile |>.mp hsourceNash
    change
      (H.terminalContinuationGameForm hNoChanceH
        (e.historyIso.stateEquiv sourceRoot)
        (hterminatesH
          (e.historyIso.stateEquiv sourceRoot)
          ((e.map_designatedContinuationRoot sourceRoot).mp hsourceRoot))).IsNash
        utility (e.mapProfile profile) at hmapped
    exact hmapped
  · intro hspe sourceRoot hsourceRoot
    have htargetRoot :
        H.IsDesignatedContinuationRoot (e.historyIso.stateEquiv sourceRoot) :=
      (e.map_designatedContinuationRoot sourceRoot).mp hsourceRoot
    have htargetNash :=
      hspe (e.historyIso.stateEquiv sourceRoot) htargetRoot
    exact
      GameForm.Iso.isNash_iff
        (e.terminalContinuationGameFormIso
          hNoChanceG hNoChanceH sourceRoot
          (hterminatesG sourceRoot hsourceRoot)
          (hterminatesH
            (e.historyIso.stateEquiv sourceRoot) htargetRoot))
        (e.terminalContinuationGameFormIso_utilityCompatible
          hNoChanceG hNoChanceH utility sourceRoot
          (hterminatesG sourceRoot hsourceRoot)
          (hterminatesH
            (e.historyIso.stateEquiv sourceRoot) htargetRoot))
        profile |>.mpr htargetNash

/-- Strict structural observed-EFG isomorphism transports a lawful subgame
system and preserves total pure-strategy equilibrium on that system in both
directions. -/
theorem isPureSubgamePerfectOn_iff
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (hNoChanceG : G.base.NoChance)
    (hNoChanceH : H.base.NoChance)
    (system : G.SubgameSystem)
    (hterminatesG : G.PureTerminatingOn hNoChanceG system)
    (utility : (N → U) → N → V)
    (profile : G.PureProfile) :
    G.IsPureSubgamePerfectOn
        hNoChanceG system hterminatesG utility profile ↔
      H.IsPureSubgamePerfectOn hNoChanceH
        (e.mapSubgameSystem system)
        (e.map_pureTerminatingOn
          hNoChanceG hNoChanceH system hterminatesG)
        utility (e.mapProfile profile) := by
  let hterminatesH :=
    e.map_pureTerminatingOn
      hNoChanceG hNoChanceH system hterminatesG
  constructor
  · intro hspe targetRoot htargetRoot
    obtain ⟨sourceRoot, rfl⟩ :=
      e.historyIso.stateEquiv.surjective targetRoot
    have hsourceRoot : system.IsRoot sourceRoot := by
      change
        system.IsRoot
          (e.historyIso.stateEquiv.symm
            (e.historyIso.stateEquiv sourceRoot))
        at htargetRoot
      simpa using htargetRoot
    have hsourceNash := hspe sourceRoot hsourceRoot
    have hmapped :=
      GameForm.Iso.isNash_iff
        (e.terminalContinuationGameFormIso
          hNoChanceG hNoChanceH sourceRoot
          (hterminatesG sourceRoot hsourceRoot)
          (hterminatesH
            (e.historyIso.stateEquiv sourceRoot)
            htargetRoot))
        (e.terminalContinuationGameFormIso_utilityCompatible
          hNoChanceG hNoChanceH utility sourceRoot
          (hterminatesG sourceRoot hsourceRoot)
          (hterminatesH
            (e.historyIso.stateEquiv sourceRoot)
            htargetRoot))
        profile |>.mp hsourceNash
    change
      (H.terminalContinuationGameForm hNoChanceH
        (e.historyIso.stateEquiv sourceRoot)
        (hterminatesH
          (e.historyIso.stateEquiv sourceRoot)
          htargetRoot)).IsNash
        utility (e.mapProfile profile) at hmapped
    exact hmapped
  · intro hspe sourceRoot hsourceRoot
    have htargetRoot :
        (e.mapSubgameSystem system).IsRoot
          (e.historyIso.stateEquiv sourceRoot) := by
      change
        system.IsRoot
          (e.historyIso.stateEquiv.symm
            (e.historyIso.stateEquiv sourceRoot))
      simpa
    have htargetNash :=
      hspe (e.historyIso.stateEquiv sourceRoot) htargetRoot
    exact
      GameForm.Iso.isNash_iff
        (e.terminalContinuationGameFormIso
          hNoChanceG hNoChanceH sourceRoot
          (hterminatesG sourceRoot hsourceRoot)
          (hterminatesH
            (e.historyIso.stateEquiv sourceRoot) htargetRoot))
        (e.terminalContinuationGameFormIso_utilityCompatible
          hNoChanceG hNoChanceH utility sourceRoot
          (hterminatesG sourceRoot hsourceRoot)
          (hterminatesH
            (e.historyIso.stateEquiv sourceRoot) htargetRoot))
        profile |>.mpr htargetNash

/-- Strict observed-EFG isomorphisms preserve complete standard pure SPE in
both directions. -/
theorem isPureStandardSubgamePerfect_iff
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(s : G.base.State) → Decidable (G.base.isTerminal s)]
    [(t : H.base.State) → Decidable (H.base.isTerminal t)]
    (e : G.Iso H)
    (hNoChanceG : G.base.NoChance)
    (hNoChanceH : H.base.NoChance)
    (system : G.CompleteSubgameSystem)
    (hterminatesG :
      G.PureTerminatingOn hNoChanceG system.toSubgameSystem)
    (utility : (N → U) → N → V)
    (profile : G.PureProfile) :
    G.IsPureStandardSubgamePerfect
        hNoChanceG system hterminatesG utility profile ↔
      H.IsPureStandardSubgamePerfect hNoChanceH
        (e.mapCompleteSubgameSystem system)
        (e.map_pureTerminatingOn
          hNoChanceG hNoChanceH system.toSubgameSystem hterminatesG)
        utility (e.mapProfile profile) := by
  simpa [IsPureStandardSubgamePerfect, mapCompleteSubgameSystem] using
    e.isPureSubgamePerfectOn_iff
      hNoChanceG hNoChanceH system.toSubgameSystem
      hterminatesG utility profile

end Iso

end ExtensiveGame.ObservedGame
