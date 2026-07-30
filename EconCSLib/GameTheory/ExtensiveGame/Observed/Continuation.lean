/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.GameForm.Continuation.Iso
import EconCSLib.GameTheory.ExtensiveGame.Observed.BehaviorRefinement.Execution

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.Continuation

Compile observed extensive games into representation-neutral continuation
semantics.

The structural observed-EFG layer remembers complete histories, observations,
public states, decision information, chance kernels, and
presentation-designated continuation roots. The `ContinuationGameForm` layer
remembers only the strategic data needed to state Nash optimality on
caller-declared roots: one shared complete strategy space, a root predicate,
and the outcome generated from every root. It cannot certify standard
subgames without a representation-aware adapter.

This module connects the two layers for:

* bounded no-chance pure continuation semantics;
* bounded chance-aware behavioral continuation semantics;
* strict observed-EFG isomorphisms;
* one-way information refinements.

The adapters expose why equilibrium proofs need not be repeated for every EFG
representation. Exact history/payoff naturality supplies the evaluator square;
root preservation supplies the declared-root map; the generic
`ContinuationGameForm` theorems then transfer Nash on
presentation-designated continuations. Information refinements reflect Nash
on presentation-designated continuations by default and become two-way
exactly when their strategy lift is surjective. Strict isomorphisms supply
both surjectivities automatically.

## Public-entry policy

Downstream strict-isomorphism clients should use the canonical relation-local
theorems `ObservedGame.Iso.isPureNashOnDesignatedContinuationsAtFuel_iff` and
`ObservedChanceGame.Iso.isBehavioralNashOnDesignatedContinuationsAtFuel_iff`.  The
private route regressions in this module check that compilation to
`ContinuationGameForm` recovers the canonical result, but they are not a
second public entry point.

## Main definitions

* `ObservedGame.pureContinuationFamily`.
* `ObservedChanceGame.behavioralContinuationFamily`.
* `ObservedGame.Iso.pureContinuationFamilyIso`.
* `ObservedGame.InformationRefinement.pureContinuationFamilyHom`.
* `ObservedGame.InformationRefinement.pureContinuationFamilySimulation`.
* `ObservedChanceGame.Iso.behavioralContinuationFamilyIso`.
* `ObservedChanceGame.InformationRefinement.behavioralContinuationFamilyHom`.
* `ObservedChanceGame.InformationRefinement.behavioralContinuationFamilySimulation`.

## Main results

* `isPureNashOnDesignatedContinuationsAtFuel_iff_continuationFamily`.
* `isBehavioralNashOnDesignatedContinuationsAtFuel_iff_continuationFamily`.
* the strict-iso adapters inherit generic two-way Nash on presentation-designated continuations transfer;
* the refinement adapters inherit generic Nash on presentation-designated continuations reflection and conditional
  two-way transfer;
* private route regressions verify the continuation-family derivations without
  adding competing downstream entry points.
-/

namespace ExtensiveGame

universe uV

/-! ### Bounded pure continuation semantics -/

namespace ObservedGame

variable {N U : Type*}

/-- The representation-neutral family of all bounded pure continuations of a
no-chance observed game. -/
def pureContinuationFamily
    (G : ObservedGame N U)
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    (hNoChance : G.base.NoChance)
    (fuel : ℕ) :
    ContinuationGameForm N where
  Strategy := G.PureStrategy
  Root :=
    G.base.toArena.HistoryFrom G.base.init
  IsDeclaredRoot := G.IsDesignatedContinuationRoot
  Outcome := Option (N → U)
  outcome := fun current profile =>
    G.stoppedPayoffFrom
      profile hNoChance current fuel

/-- Fixing a root in the pure continuation family recovers the existing
bounded continuation game form definitionally. -/
theorem pureContinuationFamily_toGameForm
    (G : ObservedGame N U)
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    (hNoChance : G.base.NoChance)
    (fuel : ℕ)
    (current :
      G.base.toArena.HistoryFrom G.base.init) :
    (G.pureContinuationFamily
      hNoChance fuel).toGameForm current =
      G.continuationGameForm
        hNoChance current fuel :=
  rfl

/-- The existing bounded pure Nash on presentation-designated continuations predicate is exactly the
representation-neutral continuation-family predicate. -/
theorem isPureNashOnDesignatedContinuationsAtFuel_iff_continuationFamily
    {V : Type uV} [DecidableEq N] [Preorder V]
    (G : ObservedGame N U)
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    (hNoChance : G.base.NoChance)
    (utility : Option (N → U) → N → V)
    (profile : G.PureProfile)
    (fuel : ℕ) :
    G.IsPureNashOnDesignatedContinuationsAtFuel
        hNoChance utility profile fuel ↔
      (G.pureContinuationFamily
        hNoChance fuel).IsNashOnRoots
          (fun _ => utility) profile :=
  Iff.rfl

namespace Iso

variable {G H : ObservedGame N U}

/-- A strict observed-EFG isomorphism induces an isomorphism of the complete
bounded pure continuation families, not merely separate isomorphisms at
individual roots. -/
def pureContinuationFamilyIso
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (e : G.Iso H)
    (hNoChanceG : G.base.NoChance)
    (hNoChanceH : H.base.NoChance)
    (fuel : ℕ) :
    (G.pureContinuationFamily
      hNoChanceG fuel).Iso
      (H.pureContinuationFamily
        hNoChanceH fuel) where
  rootEquiv :=
    e.historyIso.stateEquiv
  strategyEquiv :=
    e.strategyEquiv
  outcomeEquiv :=
    Equiv.refl _
  map_declaredRoot :=
    e.map_designatedContinuationRoot
  map_outcome := by
    intro current profile
    exact
      (e.map_stoppedPayoffFrom
        profile hNoChanceG hNoChanceH
        current fuel).symm

/-- The pure continuation-family isomorphism preserves a common
root-independent outcome utility. -/
theorem pureContinuationFamilyIso_utilityCompatible
    {V : Type uV}
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (e : G.Iso H)
    (hNoChanceG : G.base.NoChance)
    (hNoChanceH : H.base.NoChance)
    (utility : Option (N → U) → N → V)
    (fuel : ℕ) :
    (e.pureContinuationFamilyIso
      hNoChanceG hNoChanceH fuel
      ).toHom.UtilityCompatible
        (fun _ => utility)
        (fun _ => utility) := by
  intro root outcome i
  rfl

/-- Route-regression theorem: strict observed-EFG pure Nash on presentation-designated continuations transfer is an
instance of the representation-neutral continuation-family theorem.

Downstream code should use
`ObservedGame.Iso.isPureNashOnDesignatedContinuationsAtFuel_iff`; this independently proved
variant is retained to test coherence of the continuation adapter. -/
private theorem isPureNashOnDesignatedContinuationsAtFuel_iff_viaContinuationFamily
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (e : G.Iso H)
    (hNoChanceG : G.base.NoChance)
    (hNoChanceH : H.base.NoChance)
    (utility : Option (N → U) → N → V)
    (profile : G.PureProfile)
    (fuel : ℕ) :
    G.IsPureNashOnDesignatedContinuationsAtFuel
        hNoChanceG utility profile fuel ↔
      H.IsPureNashOnDesignatedContinuationsAtFuel
        hNoChanceH utility
        (e.mapProfile profile) fuel := by
  change
    (G.pureContinuationFamily
      hNoChanceG fuel).IsNashOnRoots
        (fun _ => utility) profile ↔
      (H.pureContinuationFamily
        hNoChanceH fuel).IsNashOnRoots
          (fun _ => utility)
          ((e.pureContinuationFamilyIso
            hNoChanceG hNoChanceH fuel
            ).mapProfile profile)
  exact
    (e.pureContinuationFamilyIso
      hNoChanceG hNoChanceH fuel
      ).isNashOnRoots_iff
        (e.pureContinuationFamilyIso_utilityCompatible
          hNoChanceG hNoChanceH utility fuel)
        profile

end Iso

namespace InformationRefinement

variable {G H : ObservedGame N U}

/-- An observed information refinement induces one semantic morphism between
the complete bounded pure continuation families. -/
def pureContinuationFamilyHom
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hNoChanceG : G.base.NoChance)
    (hNoChanceH : H.base.NoChance)
    (fuel : ℕ) :
    (G.pureContinuationFamily
      hNoChanceG fuel).Hom
      (H.pureContinuationFamily
        hNoChanceH fuel) where
  rootMap :=
    r.historyIso.stateEquiv
  strategyMap :=
    r.mapStrategy
  outcomeMap :=
    id
  map_declaredRoot := by
    intro current hroot
    exact
      (r.map_designatedContinuationRoot current).mp hroot
  map_outcome := by
    intro current profile
    exact
      (r.map_stoppedPayoffFrom
        profile hNoChanceG hNoChanceH
        current fuel).symm

/-- A pure refinement morphism preserves a common root-independent utility. -/
theorem pureContinuationFamilyHom_utilityCompatible
    {V : Type uV}
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hNoChanceG : G.base.NoChance)
    (hNoChanceH : H.base.NoChance)
    (utility : Option (N → U) → N → V)
    (fuel : ℕ) :
    (r.pureContinuationFamilyHom
      hNoChanceG hNoChanceH fuel
      ).UtilityCompatible
        (fun _ => utility)
        (fun _ => utility) := by
  intro root outcome i
  rfl

/-- History equivalence and exact designated-root correspondence make every
pure refinement morphism surjective on declared continuation roots. -/
theorem pureContinuationFamilyHom_declaredRootSurjective
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hNoChanceG : G.base.NoChance)
    (hNoChanceH : H.base.NoChance)
    (fuel : ℕ) :
    (r.pureContinuationFamilyHom
      hNoChanceG hNoChanceH fuel
      ).DeclaredRootSurjective := by
  intro targetRoot htargetRoot
  let sourceRoot :=
    r.historyIso.stateEquiv.symm
      targetRoot
  refine
    ⟨sourceRoot, ?_, ?_⟩
  · exact
      (r.map_designatedContinuationRoot sourceRoot).mpr
        (by
          simpa [sourceRoot] using
            htargetRoot)
  · exact
      r.historyIso.stateEquiv.apply_symm_apply
        targetRoot

/-- Exact designated-root correspondence makes the pure refinement morphism
reflect declared-root membership along its root map. -/
theorem pureContinuationFamilyHom_declaredRootReflecting
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hNoChanceG : G.base.NoChance)
    (hNoChanceH : H.base.NoChance)
    (fuel : ℕ) :
    (r.pureContinuationFamilyHom
      hNoChanceG hNoChanceH fuel
      ).DeclaredRootReflecting := by
  intro sourceRoot htargetRoot
  exact
    (r.map_designatedContinuationRoot sourceRoot).mpr
      htargetRoot

/-- The functional pure refinement adapter, regarded uniformly as a
relational-root continuation simulation.

This form composes directly with weak/stuttering compiler simulations. -/
def pureContinuationFamilySimulation
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hNoChanceG : G.base.NoChance)
    (hNoChanceH : H.base.NoChance)
    (fuel : ℕ) :
    (G.pureContinuationFamily
      hNoChanceG fuel).Simulation
      (H.pureContinuationFamily
        hNoChanceH fuel) :=
  (r.pureContinuationFamilyHom
      hNoChanceG hNoChanceH fuel
    ).toSimulation
      (r.pureContinuationFamilyHom_declaredRootReflecting
        hNoChanceG hNoChanceH fuel)

/-- The pure refinement graph simulation covers all admissible source roots. -/
theorem pureContinuationFamilySimulation_sourceRootTotal
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hNoChanceG : G.base.NoChance)
    (hNoChanceH : H.base.NoChance)
    (fuel : ℕ) :
    (r.pureContinuationFamilySimulation
      hNoChanceG hNoChanceH fuel
      ).SourceRootTotal :=
  (r.pureContinuationFamilyHom
      hNoChanceG hNoChanceH fuel
    ).toSimulation_sourceRootTotal _

/-- The pure refinement graph simulation covers all admissible target roots. -/
theorem pureContinuationFamilySimulation_targetRootTotal
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hNoChanceG : G.base.NoChance)
    (hNoChanceH : H.base.NoChance)
    (fuel : ℕ) :
    (r.pureContinuationFamilySimulation
      hNoChanceG hNoChanceH fuel
      ).TargetRootTotal :=
  (r.pureContinuationFamilyHom
      hNoChanceG hNoChanceH fuel
    ).toSimulation_targetRootTotal _
      (r.pureContinuationFamilyHom_declaredRootSurjective
        hNoChanceG hNoChanceH fuel)

/-- Regression theorem: pure Nash on presentation-designated continuations reflection along an information refinement
also follows through the graph-simulation adapter.

This path is composition-ready with genuinely relational compiler
simulations. -/
private theorem isPureNashOnDesignatedContinuationsAtFuel_of_map_viaContinuationSimulation
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hNoChanceG : G.base.NoChance)
    (hNoChanceH : H.base.NoChance)
    (utility : Option (N → U) → N → V)
    (profile : G.PureProfile)
    (fuel : ℕ)
    (hSPE :
      H.IsPureNashOnDesignatedContinuationsAtFuel
        hNoChanceH utility
        (r.mapProfile profile) fuel) :
    G.IsPureNashOnDesignatedContinuationsAtFuel
      hNoChanceG utility profile fuel := by
  change
    (G.pureContinuationFamily
      hNoChanceG fuel).IsNashOnRoots
        (fun _ => utility) profile
  apply
    ContinuationGameForm.IsNashOnRoots.comapSimulation
      (r.pureContinuationFamilySimulation
        hNoChanceG hNoChanceH fuel)
      ((r.pureContinuationFamilyHom
          hNoChanceG hNoChanceH fuel
          ).toSimulation_utilityCompatible
            _
            (r.pureContinuationFamilyHom_utilityCompatible
              hNoChanceG hNoChanceH utility fuel))
      (r.pureContinuationFamilySimulation_sourceRootTotal
        hNoChanceG hNoChanceH fuel)
  exact hSPE

/-- The pure continuation-family morphism is strategy-surjective precisely
under the refinement's explicit deviation-lifting hypothesis. -/
theorem pureContinuationFamilyHom_strategySurjective
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hNoChanceG : G.base.NoChance)
    (hNoChanceH : H.base.NoChance)
    (fuel : ℕ)
    (hsurjective : r.StrategySurjective) :
    (r.pureContinuationFamilyHom
      hNoChanceG hNoChanceH fuel
      ).StrategySurjective := by
  intro i targetStrategy
  exact hsurjective i targetStrategy

/-- Regression theorem: default fine-to-coarse pure Nash on presentation-designated continuations reflection is the
generic `ContinuationGameForm.IsNashOnRoots.comap` theorem. -/
private theorem isPureNashOnDesignatedContinuationsAtFuel_of_map_viaContinuationFamily
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hNoChanceG : G.base.NoChance)
    (hNoChanceH : H.base.NoChance)
    (utility : Option (N → U) → N → V)
    (profile : G.PureProfile)
    (fuel : ℕ)
    (hSPE :
      H.IsPureNashOnDesignatedContinuationsAtFuel
        hNoChanceH utility
        (r.mapProfile profile) fuel) :
    G.IsPureNashOnDesignatedContinuationsAtFuel
      hNoChanceG utility profile fuel := by
  change
    (G.pureContinuationFamily
      hNoChanceG fuel).IsNashOnRoots
        (fun _ => utility) profile
  apply
    ContinuationGameForm.IsNashOnRoots.comap
      (r.pureContinuationFamilyHom
        hNoChanceG hNoChanceH fuel)
      (r.pureContinuationFamilyHom_utilityCompatible
        hNoChanceG hNoChanceH utility fuel)
  exact hSPE

/-- Regression theorem: under pure deviation lifting, two-way refinement Nash on presentation-designated continuations
transfer is the generic continuation-family surjectivity theorem. -/
private theorem
    isPureNashOnDesignatedContinuationsAtFuel_iff_of_strategySurjective_viaContinuationFamily
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(state : G.base.State) →
      Decidable (G.base.isTerminal state)]
    [(state : H.base.State) →
      Decidable (H.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hNoChanceG : G.base.NoChance)
    (hNoChanceH : H.base.NoChance)
    (hsurjective : r.StrategySurjective)
    (utility : Option (N → U) → N → V)
    (profile : G.PureProfile)
    (fuel : ℕ) :
    G.IsPureNashOnDesignatedContinuationsAtFuel
        hNoChanceG utility profile fuel ↔
      H.IsPureNashOnDesignatedContinuationsAtFuel
        hNoChanceH utility
        (r.mapProfile profile) fuel := by
  change
    (G.pureContinuationFamily
      hNoChanceG fuel).IsNashOnRoots
        (fun _ => utility) profile ↔
      (H.pureContinuationFamily
        hNoChanceH fuel).IsNashOnRoots
          (fun _ => utility)
          ((r.pureContinuationFamilyHom
            hNoChanceG hNoChanceH fuel
            ).mapProfile profile)
  exact
    (r.pureContinuationFamilyHom
      hNoChanceG hNoChanceH fuel
      ).isNashOnRoots_iff_of_surjective
        (r.pureContinuationFamilyHom_utilityCompatible
          hNoChanceG hNoChanceH utility fuel)
        (r.pureContinuationFamilyHom_strategySurjective
          hNoChanceG hNoChanceH fuel
          hsurjective)
        (r.pureContinuationFamilyHom_declaredRootSurjective
          hNoChanceG hNoChanceH fuel)
        profile

end InformationRefinement

end ObservedGame

/-! ### Bounded behavioral continuation semantics -/

namespace ObservedChanceGame

variable {N U : Type*}

/-- The representation-neutral family of all bounded behavioral
continuations of an observed chance game. -/
noncomputable def behavioralContinuationFamily
    (G : ObservedChanceGame N U)
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (fuel : ℕ) :
    ContinuationGameForm N where
  Strategy :=
    G.observed.BehavioralStrategy
  Root :=
    G.observed.base.toArena.HistoryFrom
      G.observed.base.init
  IsDeclaredRoot :=
    G.observed.IsDesignatedContinuationRoot
  Outcome :=
    PMF (Option (N → U))
  outcome := fun current profile =>
    G.behavioralStoppedPayoffLawFrom
      profile current fuel

/-- Fixing a root in the behavioral continuation family recovers the existing
bounded behavioral continuation game form definitionally. -/
theorem behavioralContinuationFamily_toGameForm
    (G : ObservedChanceGame N U)
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (fuel : ℕ)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init) :
    (G.behavioralContinuationFamily
      fuel).toGameForm current =
      G.behavioralContinuationGameForm
        current fuel :=
  rfl

/-- The existing bounded behavioral Nash on presentation-designated continuations predicate is exactly the
representation-neutral continuation-family predicate. -/
theorem isBehavioralNashOnDesignatedContinuationsAtFuel_iff_continuationFamily
    {V : Type uV} [DecidableEq N] [Preorder V]
    (G : ObservedChanceGame N U)
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (utility :
      PMF (Option (N → U)) → N → V)
    (profile : G.observed.BehavioralProfile)
    (fuel : ℕ) :
    G.IsBehavioralNashOnDesignatedContinuationsAtFuel
        utility profile fuel ↔
      (G.behavioralContinuationFamily
        fuel).IsNashOnRoots
          (fun _ => utility) profile :=
  Iff.rfl

namespace Iso

variable {G H : ObservedChanceGame N U}

/-- A strict observed chance-EFG isomorphism induces an isomorphism of the
complete bounded behavioral continuation families. -/
noncomputable def behavioralContinuationFamilyIso
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (e : G.Iso H)
    (fuel : ℕ) :
    (G.behavioralContinuationFamily
      fuel).Iso
      (H.behavioralContinuationFamily
        fuel) where
  rootEquiv :=
    e.observedIso.historyIso.stateEquiv
  strategyEquiv :=
    e.observedIso.behavioralStrategyEquiv
  outcomeEquiv :=
    Equiv.refl _
  map_declaredRoot :=
    e.observedIso.map_designatedContinuationRoot
  map_outcome := by
    intro current profile
    exact
      (e.map_behavioralStoppedPayoffLawFrom
        profile current fuel).symm

/-- The behavioral continuation-family isomorphism preserves a common
root-independent functional on payoff laws. -/
theorem behavioralContinuationFamilyIso_utilityCompatible
    {V : Type uV}
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (e : G.Iso H)
    (utility :
      PMF (Option (N → U)) → N → V)
    (fuel : ℕ) :
    (e.behavioralContinuationFamilyIso
      fuel).toHom.UtilityCompatible
        (fun _ => utility)
        (fun _ => utility) := by
  intro root outcome i
  rfl

/-- Route-regression theorem: strict behavioral Nash on presentation-designated continuations transfer follows from the
generic continuation-family isomorphism theorem.

Downstream code should use
`ObservedChanceGame.Iso.isBehavioralNashOnDesignatedContinuationsAtFuel_iff`; this
independently proved variant is retained to test coherence of the continuation
adapter. -/
private theorem isBehavioralNashOnDesignatedContinuationsAtFuel_iff_viaContinuationFamily
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (e : G.Iso H)
    (utility :
      PMF (Option (N → U)) → N → V)
    (profile : G.observed.BehavioralProfile)
    (fuel : ℕ) :
    G.IsBehavioralNashOnDesignatedContinuationsAtFuel
        utility profile fuel ↔
      H.IsBehavioralNashOnDesignatedContinuationsAtFuel
        utility
        (e.observedIso.mapBehavioralProfile
          profile)
        fuel := by
  change
    (G.behavioralContinuationFamily
      fuel).IsNashOnRoots
        (fun _ => utility) profile ↔
      (H.behavioralContinuationFamily
        fuel).IsNashOnRoots
          (fun _ => utility)
          ((e.behavioralContinuationFamilyIso
            fuel).mapProfile profile)
  exact
    (e.behavioralContinuationFamilyIso
      fuel).isNashOnRoots_iff
        (e.behavioralContinuationFamilyIso_utilityCompatible
          utility fuel)
        profile

end Iso

namespace InformationRefinement

variable {G H : ObservedChanceGame N U}

/-- A chance-aware information refinement induces one semantic morphism
between the complete bounded behavioral continuation families. -/
noncomputable def behavioralContinuationFamilyHom
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (fuel : ℕ) :
    (G.behavioralContinuationFamily
      fuel).Hom
      (H.behavioralContinuationFamily
        fuel) where
  rootMap :=
    r.observedRefinement.historyIso.stateEquiv
  strategyMap :=
    r.observedRefinement.mapBehavioralStrategy
  outcomeMap :=
    id
  map_declaredRoot := by
    intro current hroot
    exact
      (r.observedRefinement.map_designatedContinuationRoot
        current).mp hroot
  map_outcome := by
    intro current profile
    exact
      (r.map_behavioralStoppedPayoffLawFrom
        profile current fuel).symm

/-- A behavioral refinement morphism preserves a common root-independent
functional on payoff laws. -/
theorem behavioralContinuationFamilyHom_utilityCompatible
    {V : Type uV}
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (utility :
      PMF (Option (N → U)) → N → V)
    (fuel : ℕ) :
    (r.behavioralContinuationFamilyHom
      fuel).UtilityCompatible
        (fun _ => utility)
        (fun _ => utility) := by
  intro root outcome i
  rfl

/-- Every behavioral refinement morphism is surjective on admissible
continuation roots because the strict history dynamics are equivalent. -/
theorem behavioralContinuationFamilyHom_declaredRootSurjective
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (fuel : ℕ) :
    (r.behavioralContinuationFamilyHom
      fuel).DeclaredRootSurjective := by
  intro targetRoot htargetRoot
  let sourceRoot :=
    r.observedRefinement.historyIso.stateEquiv.symm
      targetRoot
  refine
    ⟨sourceRoot, ?_, ?_⟩
  · exact
      (r.observedRefinement.map_designatedContinuationRoot
        sourceRoot).mpr
        (by
          simpa [sourceRoot] using
            htargetRoot)
  · exact
      r.observedRefinement.historyIso.stateEquiv.apply_symm_apply
        targetRoot

/-- Exact designated-root correspondence makes the behavioral refinement
morphism reflect declared-root membership along its root map. -/
theorem behavioralContinuationFamilyHom_declaredRootReflecting
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (fuel : ℕ) :
    (r.behavioralContinuationFamilyHom
      fuel).DeclaredRootReflecting := by
  intro sourceRoot htargetRoot
  exact
    (r.observedRefinement.map_designatedContinuationRoot
      sourceRoot).mpr htargetRoot

/-- The functional behavioral refinement adapter, regarded uniformly as a
relational-root continuation simulation.

This is the semantic form used to compose an information refinement after a
weak/stuttering compiler bridge. -/
noncomputable def behavioralContinuationFamilySimulation
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (fuel : ℕ) :
    (G.behavioralContinuationFamily
      fuel).Simulation
      (H.behavioralContinuationFamily
        fuel) :=
  (r.behavioralContinuationFamilyHom
      fuel).toSimulation
        (r.behavioralContinuationFamilyHom_declaredRootReflecting
          fuel)

/-- The behavioral refinement graph simulation covers every admissible source
root. -/
theorem behavioralContinuationFamilySimulation_sourceRootTotal
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (fuel : ℕ) :
    (r.behavioralContinuationFamilySimulation
      fuel).SourceRootTotal :=
  (r.behavioralContinuationFamilyHom
      fuel).toSimulation_sourceRootTotal _

/-- The behavioral refinement graph simulation covers every admissible target
root. -/
theorem behavioralContinuationFamilySimulation_targetRootTotal
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (fuel : ℕ) :
    (r.behavioralContinuationFamilySimulation
      fuel).TargetRootTotal :=
  (r.behavioralContinuationFamilyHom
      fuel).toSimulation_targetRootTotal _
        (r.behavioralContinuationFamilyHom_declaredRootSurjective
          fuel)

/-- Regression theorem: behavioral Nash on presentation-designated continuations reflection along an information
refinement also follows through the graph-simulation adapter. -/
private theorem
    isBehavioralNashOnDesignatedContinuationsAtFuel_of_map_viaContinuationSimulation
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (utility :
      PMF (Option (N → U)) → N → V)
    (profile : G.observed.BehavioralProfile)
    (fuel : ℕ)
    (hSPE :
      H.IsBehavioralNashOnDesignatedContinuationsAtFuel
        utility
        (r.observedRefinement.mapBehavioralProfile
          profile)
        fuel) :
    G.IsBehavioralNashOnDesignatedContinuationsAtFuel
      utility profile fuel := by
  change
    (G.behavioralContinuationFamily
      fuel).IsNashOnRoots
        (fun _ => utility) profile
  apply
    ContinuationGameForm.IsNashOnRoots.comapSimulation
      (r.behavioralContinuationFamilySimulation fuel)
      ((r.behavioralContinuationFamilyHom
          fuel).toSimulation_utilityCompatible
            _
            (r.behavioralContinuationFamilyHom_utilityCompatible
              utility fuel))
      (r.behavioralContinuationFamilySimulation_sourceRootTotal
        fuel)
  exact hSPE

/-- Behavioral strategy lifting is surjective exactly under the explicit
deviation-lifting hypothesis of the information refinement. -/
theorem behavioralContinuationFamilyHom_strategySurjective
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (fuel : ℕ)
    (hsurjective :
      r.observedRefinement.BehavioralStrategySurjective) :
    (r.behavioralContinuationFamilyHom
      fuel).StrategySurjective := by
  intro i targetStrategy
  exact hsurjective i targetStrategy

/-- Regression theorem: behavioral Nash on presentation-designated continuations reflection along an information
refinement is the generic continuation-family comap theorem. -/
private theorem isBehavioralNashOnDesignatedContinuationsAtFuel_of_map_viaContinuationFamily
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (utility :
      PMF (Option (N → U)) → N → V)
    (profile : G.observed.BehavioralProfile)
    (fuel : ℕ)
    (hSPE :
      H.IsBehavioralNashOnDesignatedContinuationsAtFuel
        utility
        (r.observedRefinement.mapBehavioralProfile
          profile)
        fuel) :
    G.IsBehavioralNashOnDesignatedContinuationsAtFuel
      utility profile fuel := by
  change
    (G.behavioralContinuationFamily
      fuel).IsNashOnRoots
        (fun _ => utility) profile
  apply
    ContinuationGameForm.IsNashOnRoots.comap
      (r.behavioralContinuationFamilyHom
        fuel)
      (r.behavioralContinuationFamilyHom_utilityCompatible
        utility fuel)
  exact hSPE

/-- Regression theorem: under behavioral deviation lifting, two-way
refinement Nash on presentation-designated continuations transfer is the generic continuation-family surjectivity
theorem. -/
private theorem
    isBehavioralNashOnDesignatedContinuationsAtFuel_iff_of_strategySurjective_viaContinuationFamily
    {V : Type uV} [DecidableEq N] [Preorder V]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable
        (H.observed.base.isTerminal state)]
    (r : G.InformationRefinement H)
    (hsurjective :
      r.observedRefinement.BehavioralStrategySurjective)
    (utility :
      PMF (Option (N → U)) → N → V)
    (profile : G.observed.BehavioralProfile)
    (fuel : ℕ) :
    G.IsBehavioralNashOnDesignatedContinuationsAtFuel
        utility profile fuel ↔
      H.IsBehavioralNashOnDesignatedContinuationsAtFuel
        utility
        (r.observedRefinement.mapBehavioralProfile
          profile)
        fuel := by
  change
    (G.behavioralContinuationFamily
      fuel).IsNashOnRoots
        (fun _ => utility) profile ↔
      (H.behavioralContinuationFamily
        fuel).IsNashOnRoots
          (fun _ => utility)
          ((r.behavioralContinuationFamilyHom
            fuel).mapProfile profile)
  exact
    (r.behavioralContinuationFamilyHom
      fuel).isNashOnRoots_iff_of_surjective
        (r.behavioralContinuationFamilyHom_utilityCompatible
          utility fuel)
        (r.behavioralContinuationFamilyHom_strategySurjective
          fuel hsurjective)
        (r.behavioralContinuationFamilyHom_declaredRootSurjective
          fuel)
        profile

end InformationRefinement

end ObservedChanceGame

end ExtensiveGame
