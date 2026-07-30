/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.PMF.FiniteProduct

/-!
# EconCSLib.Math.Probability.PMF.DeferredSampling

Fresh-query trees and an exact deferred-decisions theorem.

A `FreshQueryTree` may terminate, draw from an arbitrary chance `PMF`, or
query one coordinate from a finite family of independent laws.  Querying
removes that key from the remaining finite set, so freshness is structural:
no branch can query one coordinate twice.

There are two semantics:

* `runOnDemand` samples a queried coordinate when the query is reached;
* `runPresampled` independently samples every initially available coordinate
  first and subsequently looks values up in that table.

`runPresampled_eq_runOnDemand` proves exact equality of the resulting `PMF`s.
Chance draws may be interleaved with adaptive coordinate queries.  The proof
uses the commutativity of PMF bind at chance nodes and the finite dependent
product split theorem at query nodes.

This module is representation-neutral.  In particular, an observed EFG with
no absent-mindedness can compile its bounded execution to a fresh-query tree,
after which mixed-plan versus behavioral deferred sampling is a direct
application of the theorem here.

## Main definitions

* `PMF.FreshQueryTree`.
* `PMF.FreshQueryTree.runOnDemand`.
* `PMF.FreshQueryTree.runPresampled`.

## Main results

* `PMF.fintypePi_finset_splitAt`.
* `PMF.FreshQueryTree.runPresampled_eq_runOnDemand`.
-/

namespace PMF

universe uι uX uR

variable {ι : Type uι} [DecidableEq ι]
variable {X : ι → Type uX} {R : Type uR}

/-- Removing the selected element from a finite set is equivalent to taking
the complement of that element inside the original finite subtype. -/
def finsetEraseEquiv (remaining : Finset ι)
    (selected : ↥remaining) :
    {i : ↥remaining // i ≠ selected} ≃
      ↥(remaining.erase selected.1) where
  toFun i :=
    ⟨i.1.1, Finset.mem_erase.mpr
      ⟨by
        intro heq
        apply i.2
        exact Subtype.ext heq,
       i.1.2⟩⟩
  invFun i :=
    ⟨⟨i.1, (Finset.mem_erase.mp i.2).2⟩,
      by
        intro heq
        exact
          (Finset.mem_erase.mp i.2).1
            (congrArg Subtype.val heq)⟩
  left_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv i := by
    apply Subtype.ext
    rfl

/-- Split a dependent table on a finite set into the selected coordinate and
the table on the erased set. -/
def finsetPiSplitAt (remaining : Finset ι)
    (selected : ↥remaining) :
    ((i : ↥remaining) → X i.1) ≃
      X selected.1 ×
        ((i : ↥(remaining.erase selected.1)) → X i.1) :=
  (Equiv.piSplitAt selected (fun i : ↥remaining => X i.1)).trans
    ((Equiv.refl (X selected.1)).prodCongr
      ((finsetEraseEquiv remaining selected).piCongr
        (fun _ => Equiv.refl _)))

/-- A finite dependent product restricted to a `Finset` splits into the
selected coordinate and the product on the erased set. -/
theorem fintypePi_finset_splitAt
    (laws : (i : ι) → PMF (X i))
    (remaining : Finset ι)
    (selected : ↥remaining) :
    (fintypePi
        (fun i : ↥remaining => laws i.1)).map
          (finsetPiSplitAt remaining selected) =
      independentPair
        (laws selected.1)
        (fintypePi
          (fun i : ↥(remaining.erase selected.1) =>
            laws i.1)) := by
  ext outcome
  rw [map_equiv_apply, fintypePi_apply,
    independentPair_apply, fintypePi_apply,
    Fintype.prod_eq_mul_prod_subtype_ne]
  have hselected :
      laws selected.1
          ((finsetPiSplitAt remaining selected).symm
            outcome selected) =
        laws selected.1 outcome.1 := by
    congr 2
    simp [finsetPiSplitAt, finsetEraseEquiv,
      Equiv.piSplitAt]
  rw [hselected]
  apply congrArg (fun mass =>
    laws selected.1 outcome.1 * mass)
  exact
    Fintype.prod_equiv
      (finsetEraseEquiv remaining selected)
      (fun i =>
        laws i.1.1
          ((finsetPiSplitAt remaining selected).symm
            outcome i.1))
      (fun i => laws i.1 (outcome.2 i))
      (by
        intro i
        simp [finsetPiSplitAt, finsetEraseEquiv,
          Equiv.piSplitAt, i.2]
        congr)

/-- A finite adaptive computation that may interleave chance draws with
queries to an independently distributed table.

The `query` constructor erases its key from `remaining`, making freshness a
typing invariant rather than an external side condition. -/
inductive FreshQueryTree (X : ι → Type uX) (R : Type uR) :
    Finset ι → Type (max uι uR (uX + 1)) where
  /-- Terminate with a result. -/
  | done {remaining : Finset ι} (result : R) :
      FreshQueryTree X R remaining
  /-- Draw an auxiliary chance outcome without consuming a query key. -/
  | chance {remaining : Finset ι} {C : Type uX}
      (law : PMF C)
      (next : C → FreshQueryTree X R remaining) :
      FreshQueryTree X R remaining
  /-- Query one still-available coordinate, then erase it. -/
  | query {remaining : Finset ι}
      (selected : ↥remaining)
      (next :
        X selected.1 →
          FreshQueryTree X R
            (remaining.erase selected.1)) :
      FreshQueryTree X R remaining

namespace FreshQueryTree

/-- Restrict a table on `remaining` to the set obtained by erasing one
selected coordinate. -/
def eraseTable {remaining : Finset ι}
    (selected : ↥remaining)
    (table : (i : ↥remaining) → X i.1) :
    (i : ↥(remaining.erase selected.1)) → X i.1 :=
  fun i =>
    table ⟨i.1, (Finset.mem_erase.mp i.2).2⟩

@[simp]
theorem finsetPiSplitAt_apply
    {remaining : Finset ι}
    (selected : ↥remaining)
    (table : (i : ↥remaining) → X i.1) :
    finsetPiSplitAt remaining selected table =
      (table selected, eraseTable selected table) := by
  apply Prod.ext
  · simp [finsetPiSplitAt, finsetEraseEquiv,
      Equiv.piSplitAt]
  · funext i
    simp [finsetPiSplitAt, finsetEraseEquiv,
      Equiv.piSplitAt, eraseTable]
    congr

@[simp]
theorem finsetPiSplitAt_symm_selected
    {remaining : Finset ι}
    (selected : ↥remaining)
    (table :
      X selected.1 ×
        ((i : ↥(remaining.erase selected.1)) → X i.1)) :
    (finsetPiSplitAt remaining selected).symm
        table selected =
      table.1 := by
  have h :=
    (finsetPiSplitAt remaining selected).apply_symm_apply
      table
  rw [finsetPiSplitAt_apply] at h
  exact congrArg Prod.fst h

@[simp]
theorem eraseTable_finsetPiSplitAt_symm
    {remaining : Finset ι}
    (selected : ↥remaining)
    (table :
      X selected.1 ×
        ((i : ↥(remaining.erase selected.1)) → X i.1)) :
    eraseTable selected
        ((finsetPiSplitAt remaining selected).symm table) =
      table.2 := by
  have h :=
    (finsetPiSplitAt remaining selected).apply_symm_apply
      table
  rw [finsetPiSplitAt_apply] at h
  exact congrArg Prod.snd h

/-- Execute chance nodes while answering query nodes from a fixed table. -/
noncomputable def runWithTable :
    {remaining : Finset ι} →
      FreshQueryTree X R remaining →
      ((i : ↥remaining) → X i.1) →
      PMF R
  | _, .done result, _ =>
      PMF.pure result
  | _, .chance law next, table =>
      law.bind fun outcome =>
        runWithTable (next outcome) table
  | _, .query selected next, table =>
      runWithTable
        (next (table selected))
        (eraseTable selected table)

/-- Execute a fresh-query tree by drawing each coordinate only when queried. -/
noncomputable def runOnDemand
    (laws : (i : ι) → PMF (X i)) :
    {remaining : Finset ι} →
      FreshQueryTree X R remaining →
      PMF R
  | _, .done result =>
      PMF.pure result
  | _, .chance law next =>
      law.bind fun outcome =>
        runOnDemand laws (next outcome)
  | _, .query selected next =>
      (laws selected.1).bind fun value =>
        runOnDemand laws (next value)

/-- Execute a fresh-query tree after independently sampling every initially
available coordinate. -/
noncomputable def runPresampled
    (laws : (i : ι) → PMF (X i))
    {remaining : Finset ι}
    (tree : FreshQueryTree X R remaining) :
    PMF R :=
  (fintypePi
    (fun i : ↥remaining => laws i.1)).bind
      (runWithTable tree)

/-- Pre-sampling all independent query answers and sampling them only when
first queried induce exactly the same result law.

The result is exact equality of `PMF`s, not merely equality of support or an
approximate coupling. -/
theorem runPresampled_eq_runOnDemand
    (laws : (i : ι) → PMF (X i)) :
    ∀ {remaining : Finset ι}
      (tree : FreshQueryTree X R remaining),
      runPresampled laws tree =
        runOnDemand laws tree := by
  intro remaining tree
  induction tree with
  | done result =>
      simp [runPresampled, runWithTable,
        runOnDemand]
  | @chance remaining C law next ih =>
      change
        (fintypePi
          (fun i : ↥remaining => laws i.1)).bind
            (fun table =>
              law.bind fun outcome =>
                runWithTable (next outcome) table) =
          law.bind fun outcome =>
            runOnDemand laws (next outcome)
      rw [PMF.bind_comm]
      apply congrArg (fun continuation =>
        law.bind continuation)
      funext outcome
      exact ih outcome
  | @query remaining selected next ih =>
      let split :=
        finsetPiSplitAt (X := X)
          remaining selected
      let remainingLaw :=
        fintypePi
          (fun i : ↥(remaining.erase selected.1) =>
            laws i.1)
      calc
        runPresampled laws (.query selected next) =
            ((fintypePi
              (fun i : ↥remaining =>
                laws i.1)).map split).bind
              (fun pair =>
                runWithTable
                  (.query selected next)
                  (split.symm pair)) := by
            rw [PMF.bind_map]
            unfold runPresampled
            apply congrArg (fun continuation =>
              (fintypePi
                (fun i : ↥remaining =>
                  laws i.1)).bind continuation)
            funext table
            change
              runWithTable (.query selected next) table =
                runWithTable (.query selected next)
                  (split.symm (split table))
            rw [Equiv.symm_apply_apply]
        _ = (independentPair
              (laws selected.1)
              remainingLaw).bind
              (fun pair =>
                runWithTable
                  (.query selected next)
                  (split.symm pair)) := by
            rw [fintypePi_finset_splitAt]
        _ = (laws selected.1).bind
              (fun value =>
                remainingLaw.bind fun table =>
                  runWithTable (next value) table) := by
            unfold independentPair
            rw [PMF.bind_bind]
            apply congrArg (fun continuation =>
              (laws selected.1).bind continuation)
            funext value
            rw [PMF.bind_map]
            apply congrArg (fun continuation =>
              remainingLaw.bind continuation)
            funext table
            simp [split, runWithTable]
        _ = (laws selected.1).bind
              (fun value =>
                runOnDemand laws (next value)) := by
            apply congrArg (fun continuation =>
              (laws selected.1).bind continuation)
            funext value
            exact ih value
        _ = runOnDemand laws
              (.query selected next) :=
            rfl

end FreshQueryTree

end PMF
