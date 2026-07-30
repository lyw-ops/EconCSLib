/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Discrete
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# EconCSLib.Examples.ExtensiveGame.ReusableSemantics

Regression examples for the reusable EFG semantic interfaces.

The first example uses `WithTop Nat` as an arbitrary index type and a
`Measure ℝ` outcome rather than a discrete `PMF`. It is only an interface smoke
test: the evaluator ignores its index, the utility is constant, and the
morphism is the identity. In particular, the distinguished `⊤` index has no
proved relationship to the finite indices and is not a limit theorem.

The second example is a consumer of `BoundedDesignatedNashBridge` alone. The same
eliminator applies to the pure, behavioral, mixed, and finite-Kuhn bridge
constructors exposed by `ObservedStrategyBridge`.
-/

namespace Examples.ReusableSemantics

open MeasureTheory

/-- A semantics with finite indices and a distinguished `⊤` index.

The constant Dirac evaluator is intentionally minimal: this regression checks
the interface boundary, not a particular convergence theorem. More elaborate
developments must supply separate convergence theorems before interpreting
`⊤` as a mathematical limit. -/
noncomputable def finiteAndDistinguishedTopSemantics :
    IndexedContinuationGameForm (Fin 1) where
  Strategy := fun _ => Bool
  Horizon := WithTop ℕ
  Root := Unit
  IsDeclaredRoot := fun _ => True
  Outcome := Measure ℝ
  outcome := fun _ _ profile =>
    Measure.dirac (if profile 0 = true then 1 else 0)

/-- A distinguished top index accepted by the generic interface. -/
def distinguishedTopIndex : WithTop ℕ :=
  ⊤

/-- A constant smoke-test utility on measure-valued outcomes. -/
def smokeUtility
    (_ : WithTop ℕ) (_ : Unit) (_ : Measure ℝ) (_ : Fin 1) : ℕ :=
  0

/-- Identity-transfer smoke test at a distinguished top index with a
measure-valued outcome. This proves only interface compatibility: it does not
construct a probability execution or establish convergence. -/
theorem measureOutcome_atTop_interface_smoke
    (profile : finiteAndDistinguishedTopSemantics.Profile) :
    finiteAndDistinguishedTopSemantics.IsNashOnRootsAt
        (smokeUtility distinguishedTopIndex)
        distinguishedTopIndex profile ↔
      finiteAndDistinguishedTopSemantics.IsNashOnRootsAt
        (smokeUtility distinguishedTopIndex)
        distinguishedTopIndex
        ((IndexedContinuationGameForm.Hom.refl
          finiteAndDistinguishedTopSemantics).mapProfile profile) := by
  exact
    (IndexedContinuationGameForm.Hom.refl
      finiteAndDistinguishedTopSemantics
      ).isNashOnRootsAt_iff_of_surjective
        (sourceUtility := smokeUtility)
        (targetUtility := smokeUtility)
        (by
          intro horizon root outcome i
          rfl)
        (fun _ => Function.surjective_id)
        (by
          intro targetRoot hroot
          exact ⟨targetRoot, hroot, rfl⟩)
        distinguishedTopIndex profile

/-- The same arbitrary-index, measure-valued interface can attach directly to
any observed EFG without rebuilding its complete-history root structure. -/
noncomputable def observedMeasureSemantics
    {N U : Type*} (G : ExtensiveGame.ObservedGame N U) :
    G.ContinuationSemantics where
  Strategy := fun _ => Unit
  Horizon := WithTop ℕ
  Outcome := Measure ℝ
  evaluate := fun _ _ _ => Measure.dirac 0

/-- The observed-semantics adapter reuses the game's admissible-subgame
predicate definitionally. -/
theorem observedMeasureSemantics_subgameRoot
    {N U : Type*} (G : ExtensiveGame.ObservedGame N U)
    (root : G.base.toArena.HistoryFrom G.base.init) :
    (observedMeasureSemantics G).toIndexedGameForm.IsDeclaredRoot root ↔
      G.IsDesignatedContinuationRoot root :=
  Iff.rfl

/-- Downstream code consumes every strategy-mode bridge through one operation,
without selecting a mode-specific transfer theorem. -/
theorem useBoundedDesignatedNashBridge
    {SourceProfile TargetProfile : Type*}
    {SourceProperty : SourceProfile → Prop}
    {TargetProperty : TargetProfile → Prop}
    (bridge :
      ExtensiveGame.BoundedDesignatedNashBridge
        SourceProfile TargetProfile SourceProperty TargetProperty)
    (profile : SourceProfile) :
    SourceProperty profile ↔
      TargetProperty (bridge.mapProfile profile) :=
  bridge.isNash_iff profile

end Examples.ReusableSemantics
