/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Refinement.Core
import EconCSLib.GameTheory.ExtensiveGame.Observed.SPE

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.Refinement.Termination

Termination-certified total continuation semantics for information refinements.
-/

namespace ExtensiveGame.ObservedGame

universe uV

variable {N U : Type*}

namespace InformationRefinement

variable {G H : ObservedGame N U}

/-! ### Termination-certified total continuation semantics -/

/-- Eventual termination of a lifted fine profile implies eventual termination
of its coarse source profile. -/
theorem pureTerminatesFrom_of_map
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (profile : G.PureProfile)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (hterminates :
      H.PureTerminatesFrom
        (r.mapProfile profile) hNoChanceH
        (r.historyIso.stateEquiv current)) :
    G.PureTerminatesFrom
      profile hNoChanceG current := by
  rcases hterminates with ⟨fuel, hterminal⟩
  refine ⟨fuel, ?_⟩
  have hmapped :
      H.base.isTerminal
        (r.historyIso.stateEquiv
          (G.stoppedHistoryFrom
            profile hNoChanceG current fuel)).1 := by
    rw [r.map_stoppedHistoryFrom
      profile hNoChanceG hNoChanceH current fuel]
    exact hterminal
  exact
    (r.isTerminal_iff
      (G.stoppedHistoryFrom
        profile hNoChanceG current fuel)).mpr hmapped

/-- Root-scoped pure termination of the finer game reflects to the coarser
game along an explicit root map.

Only lifted coarse profiles are needed for this conclusion; the fine
termination certificate may cover additional path-contingent profiles. -/
theorem reflect_pureTerminatingOnRoots
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (sourceRoots : G.RootPresentation)
    (targetRoots : H.RootPresentation)
    (hroots :
      r.MapsRootPresentations sourceRoots targetRoots)
    (hterminatesH :
      H.PureTerminatingOnRoots hNoChanceH targetRoots) :
    G.PureTerminatingOnRoots hNoChanceG sourceRoots := by
  intro sourceRoot hsourceRoot profile
  have htargetRoot :
      targetRoots.IsRoot (r.historyIso.stateEquiv sourceRoot) :=
    hroots sourceRoot hsourceRoot
  exact
    r.pureTerminatesFrom_of_map
      profile hNoChanceG hNoChanceH sourceRoot
      (hterminatesH
        (r.historyIso.stateEquiv sourceRoot)
        htargetRoot
        (r.mapProfile profile))

/-- The strict history map sends the selected coarse terminal history to the
selected fine terminal history of the lifted profile.

The two existential termination proofs may choose different fuel values;
terminal-run uniqueness identifies the resulting histories. -/
theorem map_terminalHistoryFrom
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (profile : G.PureProfile)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (hterminatesG :
      G.PureTerminatesFrom
        profile hNoChanceG current)
    (hterminatesH :
      H.PureTerminatesFrom
        (r.mapProfile profile) hNoChanceH
        (r.historyIso.stateEquiv current)) :
    r.historyIso.stateEquiv
        (G.terminalHistoryFrom
          profile hNoChanceG current hterminatesG) =
      H.terminalHistoryFrom
        (r.mapProfile profile) hNoChanceH
        (r.historyIso.stateEquiv current)
        hterminatesH := by
  let sourceFuel :=
    G.terminalFuel
      profile hNoChanceG current hterminatesG
  have hsourceTerminal :
      G.base.isTerminal
        (G.stoppedHistoryFrom
          profile hNoChanceG current sourceFuel).1 :=
    G.terminalFuel_spec
      profile hNoChanceG current hterminatesG
  have hmappedTerminal :
      H.base.isTerminal
        (H.stoppedHistoryFrom
          (r.mapProfile profile) hNoChanceH
          (r.historyIso.stateEquiv current)
          sourceFuel).1 := by
    rw [← r.map_stoppedHistoryFrom
      profile hNoChanceG hNoChanceH
      current sourceFuel]
    exact
      (r.isTerminal_iff
        (G.stoppedHistoryFrom
          profile hNoChanceG current sourceFuel)).mp
        hsourceTerminal
  calc
    r.historyIso.stateEquiv
        (G.terminalHistoryFrom
          profile hNoChanceG current hterminatesG) =
        H.stoppedHistoryFrom
          (r.mapProfile profile) hNoChanceH
          (r.historyIso.stateEquiv current)
          sourceFuel := by
      exact
        r.map_stoppedHistoryFrom
          profile hNoChanceG hNoChanceH
          current sourceFuel
    _ = H.terminalHistoryFrom
          (r.mapProfile profile) hNoChanceH
          (r.historyIso.stateEquiv current)
          hterminatesH :=
      (H.terminalHistoryFrom_eq_of_terminal
        (r.mapProfile profile) hNoChanceH
        (r.historyIso.stateEquiv current)
        hterminatesH sourceFuel
        hmappedTerminal).symm

/-- Total terminal payoffs of lifted fine profiles agree exactly with their
coarse source profiles. -/
theorem map_terminalPayoffFrom
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (profile : G.PureProfile)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (hterminatesG :
      G.PureTerminatesFrom
        profile hNoChanceG current)
    (hterminatesH :
      H.PureTerminatesFrom
        (r.mapProfile profile) hNoChanceH
        (r.historyIso.stateEquiv current)) :
    H.terminalPayoffFrom
        (r.mapProfile profile) hNoChanceH
        (r.historyIso.stateEquiv current)
        hterminatesH =
      G.terminalPayoffFrom
        profile hNoChanceG current hterminatesG := by
  change
    H.base.payoff
        (H.terminalHistoryFrom
          (r.mapProfile profile) hNoChanceH
          (r.historyIso.stateEquiv current) hterminatesH).1 =
      G.base.payoff
        (G.terminalHistoryFrom
          profile hNoChanceG current hterminatesG).1
  rw [
    ← r.map_terminalHistoryFrom
      profile hNoChanceG hNoChanceH current
      hterminatesG hterminatesH]
  exact
    r.map_payoff
      (G.terminalHistoryFrom
        profile hNoChanceG current hterminatesG)
      (G.terminalHistoryFrom_terminal
        profile hNoChanceG current hterminatesG)

/-- An information refinement induces a game-form morphism between total
continuation games whenever termination is certified on both sides. -/
noncomputable def terminalContinuationGameFormHom
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (hterminatesG :
      G.PureTerminatingAt hNoChanceG current)
    (hterminatesH :
      H.PureTerminatingAt hNoChanceH
        (r.historyIso.stateEquiv current)) :
    (G.terminalContinuationGameForm
      hNoChanceG current hterminatesG).Hom
      (H.terminalContinuationGameForm
        hNoChanceH
        (r.historyIso.stateEquiv current)
        hterminatesH) where
  strategyMap := r.mapStrategy
  outcomeMap := id
  map_outcome := by
    intro profile
    exact
      (r.map_terminalPayoffFrom
        profile hNoChanceG hNoChanceH current
        (hterminatesG profile)
        (hterminatesH (r.mapProfile profile))).symm

/-- The total continuation morphism preserves a shared payoff-utility
interpretation. -/
theorem terminalContinuationGameFormHom_utilityCompatible
    {V : Type uV}
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (utility : (N → U) → N → V)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (hterminatesG :
      G.PureTerminatingAt hNoChanceG current)
    (hterminatesH :
      H.PureTerminatingAt hNoChanceH
        (r.historyIso.stateEquiv current)) :
    GameForm.Hom.UtilityCompatible
      (r.terminalContinuationGameFormHom
        hNoChanceG hNoChanceH current
        hterminatesG hterminatesH)
      utility utility := by
  intro outcome i
  rfl

/-- Strategy surjectivity passes to total continuation game-form morphisms. -/
theorem terminalContinuationGameFormHom_strategySurjective
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (hterminatesG :
      G.PureTerminatingAt hNoChanceG current)
    (hterminatesH :
      H.PureTerminatingAt hNoChanceH
        (r.historyIso.stateEquiv current))
    (hsurjective : r.StrategySurjective) :
    (r.terminalContinuationGameFormHom
      hNoChanceG hNoChanceH current
      hterminatesG hterminatesH
      ).StrategySurjective := by
  intro i targetStrategy
  exact hsurjective i targetStrategy

/-- Nash equilibrium of a lifted fine total continuation reflects to the
coarse total continuation. -/
theorem terminalContinuationIsNash_of_map
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (utility : (N → U) → N → V)
    (profile : G.PureProfile)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (hterminatesG :
      G.PureTerminatingAt hNoChanceG current)
    (hterminatesH :
      H.PureTerminatingAt hNoChanceH
        (r.historyIso.stateEquiv current))
    (hNash :
      (H.terminalContinuationGameForm
        hNoChanceH
        (r.historyIso.stateEquiv current)
        hterminatesH).IsNash
        utility (r.mapProfile profile)) :
    (G.terminalContinuationGameForm
      hNoChanceG current hterminatesG).IsNash
      utility profile := by
  exact
    hNash.comap
      (r.terminalContinuationGameFormHom
        hNoChanceG hNoChanceH current
        hterminatesG hterminatesH)
      (r.terminalContinuationGameFormHom_utilityCompatible
        hNoChanceG hNoChanceH utility current
        hterminatesG hterminatesH)

/-- Under explicit deviation lifting, corresponding total continuations have
equivalent Nash predicates. -/
theorem terminalContinuationIsNash_iff_of_strategySurjective
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (hsurjective : r.StrategySurjective)
    (utility : (N → U) → N → V)
    (profile : G.PureProfile)
    (current : G.base.toArena.HistoryFrom G.base.init)
    (hterminatesG :
      G.PureTerminatingAt hNoChanceG current)
    (hterminatesH :
      H.PureTerminatingAt hNoChanceH
        (r.historyIso.stateEquiv current)) :
    (G.terminalContinuationGameForm
      hNoChanceG current hterminatesG).IsNash
        utility profile ↔
      (H.terminalContinuationGameForm
        hNoChanceH
        (r.historyIso.stateEquiv current)
        hterminatesH).IsNash
        utility (r.mapProfile profile) := by
  exact
    (r.terminalContinuationGameFormHom
      hNoChanceG hNoChanceH current
      hterminatesG hterminatesH
      ).isNash_iff_of_strategySurjective
        (r.terminalContinuationGameFormHom_utilityCompatible
          hNoChanceG hNoChanceH utility current
          hterminatesG hterminatesH)
        (r.terminalContinuationGameFormHom_strategySurjective
          hNoChanceG hNoChanceH current
          hterminatesG hterminatesH
          hsurjective)
        profile

/-- Total Nash on explicitly mapped roots of a lifted fine profile reflects
to total Nash on the selected coarse roots. -/
theorem isPureNashOnRoots_of_map
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (sourceRoots : G.RootPresentation)
    (targetRoots : H.RootPresentation)
    (hroots :
      r.MapsRootPresentations sourceRoots targetRoots)
    (hterminatesH :
      H.PureTerminatingOnRoots hNoChanceH targetRoots)
    (utility : (N → U) → N → V)
    (profile : G.PureProfile)
    (hSPE :
      H.IsPureNashOnRoots
        hNoChanceH targetRoots hterminatesH utility
        (r.mapProfile profile)) :
    G.IsPureNashOnRoots
      hNoChanceG sourceRoots
      (r.reflect_pureTerminatingOnRoots
        hNoChanceG hNoChanceH sourceRoots targetRoots
        hroots hterminatesH)
      utility profile := by
  intro sourceRoot hsourceRoot
  have htargetRoot :
      targetRoots.IsRoot (r.historyIso.stateEquiv sourceRoot) :=
    hroots sourceRoot hsourceRoot
  exact
    r.terminalContinuationIsNash_of_map
      hNoChanceG hNoChanceH utility profile
      sourceRoot
      ((r.reflect_pureTerminatingOnRoots
        hNoChanceG hNoChanceH sourceRoots targetRoots
        hroots hterminatesH)
        sourceRoot hsourceRoot)
      (hterminatesH
        (r.historyIso.stateEquiv sourceRoot)
        htargetRoot)
      (hSPE
        (r.historyIso.stateEquiv sourceRoot)
        htargetRoot)

/-- With strategy-surjective lifting, exact root correspondence, and
root-scoped termination certificates, total pure Nash transfers in both
directions. -/
theorem isPureNashOnRoots_iff_of_strategySurjective
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hNoChanceG : G.base.NoChanceOnHistories)
    (hNoChanceH : H.base.NoChanceOnHistories)
    (sourceRoots : G.RootPresentation)
    (targetRoots : H.RootPresentation)
    (hroots :
      r.PreservesRootPresentations sourceRoots targetRoots)
    (hterminatesG :
      G.PureTerminatingOnRoots hNoChanceG sourceRoots)
    (hterminatesH :
      H.PureTerminatingOnRoots hNoChanceH targetRoots)
    (hsurjective : r.StrategySurjective)
    (utility : (N → U) → N → V)
    (profile : G.PureProfile) :
    G.IsPureNashOnRoots
        hNoChanceG sourceRoots hterminatesG utility profile ↔
      H.IsPureNashOnRoots
        hNoChanceH targetRoots hterminatesH utility
        (r.mapProfile profile) := by
  constructor
  · intro hSPE targetRoot htargetRoot
    obtain ⟨sourceRoot, rfl⟩ :=
      r.historyIso.stateEquiv.surjective
        targetRoot
    have hsourceRoot :
        sourceRoots.IsRoot sourceRoot :=
      (hroots sourceRoot).mpr htargetRoot
    have hsourceNash :=
      hSPE sourceRoot hsourceRoot
    have hmapped :=
      (r.terminalContinuationIsNash_iff_of_strategySurjective
        hNoChanceG hNoChanceH hsurjective
        utility profile sourceRoot
        (hterminatesG sourceRoot hsourceRoot)
        (hterminatesH
          (r.historyIso.stateEquiv sourceRoot)
          ((hroots sourceRoot).mp hsourceRoot))).mp hsourceNash
    exact hmapped
  · intro hSPE sourceRoot hsourceRoot
    have htargetRoot :
        targetRoots.IsRoot
          (r.historyIso.stateEquiv sourceRoot) :=
      (hroots sourceRoot).mp hsourceRoot
    exact
      (r.terminalContinuationIsNash_iff_of_strategySurjective
        hNoChanceG hNoChanceH hsurjective
        utility profile sourceRoot
        (hterminatesG sourceRoot hsourceRoot)
        (hterminatesH
          (r.historyIso.stateEquiv sourceRoot)
          htargetRoot)).mpr
        (hSPE
          (r.historyIso.stateEquiv sourceRoot)
          htargetRoot)

end InformationRefinement

end ExtensiveGame.ObservedGame
