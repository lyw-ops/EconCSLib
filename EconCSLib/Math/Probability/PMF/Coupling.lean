/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# EconCSLib.Math.Probability.PMF.Coupling

Relation-supported couplings of discrete probability mass functions.

`PMF.RelCoupling R p q` is an exact joint PMF with first marginal `p`, second
marginal `q`, and support contained in `R`. The API keeps a coupling distinct
from equality: deterministic observables have equal laws only through
`RelCoupling.map_eq` after proving that related pairs have equal images.

## Main definitions

* `PMF.RelCoupling`;
* `PMF.independentCoupling`.

## Main results

* `PMF.relCoupling_refl`, `RelCoupling.symm`, and `relCoupling_pure`;
* `RelCoupling.map` and `RelCoupling.map_eq`;
* `RelCoupling.bind`;
* `bind_congr_support`;
* supported-witness lemmas for both marginals.
-/

namespace PMF

universe uα uβ

/-- Two continuations that agree on the support of their input PMF have the
same bind.  This support-sensitive congruence is useful for dependent
accumulator samplers, whose off-support continuations need not agree. -/
theorem bind_congr_support {α : Type uα} {β : Type uβ}
    (p : PMF α) (f g : α → PMF β)
    (h : ∀ a ∈ p.support, f a = g a) :
    p.bind f = p.bind g := by
  ext b
  rw [PMF.bind_apply, PMF.bind_apply]
  apply tsum_congr
  intro a
  by_cases ha : p a = 0
  · simp [ha]
  · rw [h a ((PMF.mem_support_iff p a).mpr ha)]

/-- A coupling of `p` and `q` supported on the binary relation `R`.

The first and second marginals are required to be exactly `p` and `q`.
The support condition then witnesses that probability mass is matched only
between related states. -/
def RelCoupling {α : Type uα} {β : Type uβ}
    (R : α → β → Prop) (p : PMF α) (q : PMF β) : Prop :=
  ∃ coupling : PMF (α × β),
    coupling.map Prod.fst = p ∧
    coupling.map Prod.snd = q ∧
    ∀ pair ∈ coupling.support, R pair.1 pair.2

/-- A PMF couples to itself along equality, using the diagonal coupling. -/
theorem relCoupling_refl {α : Type uα} (p : PMF α) :
    RelCoupling (fun a b : α => a = b) p p := by
  refine ⟨p.map (fun a => (a, a)), ?_, ?_, ?_⟩
  · simpa [PMF.map_comp, Function.comp_def] using PMF.map_id p
  · simpa [PMF.map_comp, Function.comp_def] using PMF.map_id p
  · intro pair hpair
    obtain ⟨a, _, ha⟩ :=
      (PMF.mem_support_map_iff
        (p := p) (f := fun a => (a, a)) (b := pair)).mp hpair
    subst pair
    rfl

/-- Transpose a relational coupling by swapping its two coordinates. -/
theorem RelCoupling.symm {α : Type uα} {β : Type uβ}
    {R : α → β → Prop} {p : PMF α} {q : PMF β}
    (h : RelCoupling R p q) :
    RelCoupling (fun b a => R a b) q p := by
  obtain ⟨coupling, hfst, hsnd, hsupport⟩ := h
  refine
    ⟨coupling.map (fun pair => (pair.2, pair.1)), ?_, ?_, ?_⟩
  · calc
      (coupling.map (fun pair => (pair.2, pair.1))).map Prod.fst =
          coupling.map Prod.snd := by
            rw [PMF.map_comp]
            rfl
      _ = q := hsnd
  · calc
      (coupling.map (fun pair => (pair.2, pair.1))).map Prod.snd =
          coupling.map Prod.fst := by
            rw [PMF.map_comp]
            rfl
      _ = p := hfst
  · intro pair hpair
    obtain ⟨sourcePair, hsourcePair, hmap⟩ :=
      (PMF.mem_support_map_iff
        (p := coupling) (f := fun pair => (pair.2, pair.1))
        (b := pair)).mp hpair
    subst pair
    exact hsupport sourcePair hsourcePair

/-- Every supported point of the right marginal of a relational coupling has
a supported related witness in the left marginal. -/
theorem RelCoupling.exists_left_of_mem_support_right
    {α : Type uα} {β : Type uβ}
    {R : α → β → Prop} {p : PMF α} {q : PMF β}
    (h : RelCoupling R p q)
    {right : β} (hright : right ∈ q.support) :
    ∃ left ∈ p.support, R left right := by
  obtain ⟨coupling, hfst, hsnd, hsupport⟩ := h
  have hrightMarginal :
      right ∈ (coupling.map Prod.snd).support := by
    rw [hsnd]
    exact hright
  obtain ⟨pair, hpair, hpairRight⟩ :=
    (PMF.mem_support_map_iff
      (p := coupling) (f := Prod.snd) (b := right)).mp
      hrightMarginal
  have hleftMarginal :
      pair.1 ∈ (coupling.map Prod.fst).support :=
    (PMF.mem_support_map_iff
      (p := coupling) (f := Prod.fst) (b := pair.1)).mpr
      ⟨pair, hpair, rfl⟩
  refine ⟨pair.1, ?_, ?_⟩
  · rw [hfst] at hleftMarginal
    exact hleftMarginal
  · simpa [hpairRight] using hsupport pair hpair

/-- Every supported point of the left marginal of a relational coupling has
a supported related witness in the right marginal. -/
theorem RelCoupling.exists_right_of_mem_support_left
    {α : Type uα} {β : Type uβ}
    {R : α → β → Prop} {p : PMF α} {q : PMF β}
    (h : RelCoupling R p q)
    {left : α} (hleft : left ∈ p.support) :
    ∃ right ∈ q.support, R left right :=
  h.symm.exists_left_of_mem_support_right hleft

/-- Push a relational coupling through a pair of related deterministic maps. -/
theorem RelCoupling.map
    {α : Type uα} {β : Type uβ} {γ : Type*} {δ : Type*}
    {R : α → β → Prop} {S : γ → δ → Prop}
    {p : PMF α} {q : PMF β} {f : α → γ} {g : β → δ}
    (h : RelCoupling R p q)
    (hmap : ∀ a b, R a b → S (f a) (g b)) :
    RelCoupling S (p.map f) (q.map g) := by
  obtain ⟨coupling, hfst, hsnd, hsupport⟩ := h
  refine
    ⟨coupling.map (fun pair => (f pair.1, g pair.2)), ?_, ?_, ?_⟩
  · calc
      (coupling.map (fun pair => (f pair.1, g pair.2))).map Prod.fst =
          (coupling.map Prod.fst).map f := by
            simp only [PMF.map_comp]
            rfl
      _ = p.map f := by rw [hfst]
  · calc
      (coupling.map (fun pair => (f pair.1, g pair.2))).map Prod.snd =
          (coupling.map Prod.snd).map g := by
            simp only [PMF.map_comp]
            rfl
      _ = q.map g := by rw [hsnd]
  · intro pair hpair
    obtain ⟨sourcePair, hsourcePair, hsourceMap⟩ :=
      (PMF.mem_support_map_iff
        (p := coupling)
        (f := fun pair => (f pair.1, g pair.2))
        (b := pair)).mp hpair
    subst pair
    exact hmap sourcePair.1 sourcePair.2
      (hsupport sourcePair hsourcePair)

/-- Two maps which agree on the support of a PMF have the same pushforward
law. -/
theorem map_eq_of_eq_on_support
    {α : Type uα} {β : Type uβ}
    (p : PMF α) {f g : α → β}
    (hfg : ∀ a ∈ p.support, f a = g a) :
    p.map f = p.map g := by
  ext b
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ p.support
  · rw [hfg a ha]
  · have hzero : p a = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using ha
    simp only [hzero, ite_self]

/-- Related observables have exactly equal laws under a relational coupling.

This is the main elimination principle for a coupling: once the relation says
that the two readings agree, the joint witness can be forgotten and the two
pushforward PMFs are propositionally equal. -/
theorem RelCoupling.map_eq
    {α : Type uα} {β : Type uβ} {γ : Type*}
    {R : α → β → Prop}
    {p : PMF α} {q : PMF β} {f : α → γ} {g : β → γ}
    (h : RelCoupling R p q)
    (hmap : ∀ a b, R a b → f a = g b) :
    p.map f = q.map g := by
  obtain ⟨coupling, hfst, hsnd, hsupport⟩ := h
  calc
    p.map f = (coupling.map Prod.fst).map f := by rw [hfst]
    _ = coupling.map (f ∘ Prod.fst) := PMF.map_comp _ _ _
    _ = coupling.map (g ∘ Prod.snd) := by
      apply map_eq_of_eq_on_support
      intro pair hpair
      exact hmap pair.1 pair.2 (hsupport pair hpair)
    _ = (coupling.map Prod.snd).map g := (PMF.map_comp _ _ _).symm
    _ = q.map g := by rw [hsnd]

/-- Couple two point masses whenever their atoms are related. -/
theorem relCoupling_pure {α : Type uα} {β : Type uβ}
    {R : α → β → Prop} {a : α} {b : β} (hab : R a b) :
    RelCoupling R (pure a) (pure b) := by
  refine ⟨pure (a, b), ?_, ?_, ?_⟩
  · rw [PMF.pure_map]
  · rw [PMF.pure_map]
  · intro pair hpair
    rw [mem_support_pure_iff] at hpair
    subst pair
    exact hab

/-- The independent product of two PMFs.

This is used as an arbitrary total extension when a dependent family of
couplings is only specified on the support of an outer coupling.  The
off-support branch never contributes probability mass. -/
noncomputable def independentCoupling {α : Type uα} {β : Type uβ}
    (p : PMF α) (q : PMF β) : PMF (α × β) :=
  p.bind fun a => q.map fun b => (a, b)

@[simp]
theorem independentCoupling_map_fst {α : Type uα} {β : Type uβ}
    (p : PMF α) (q : PMF β) :
    (independentCoupling p q).map Prod.fst = p := by
  rw [independentCoupling, PMF.map_bind]
  calc
    p.bind
          (fun a => (q.map fun b => (a, b)).map Prod.fst) =
        p.bind pure := by
          congr 1
          funext a
          rw [PMF.map_comp]
          change q.map (Function.const β a) = pure a
          exact PMF.map_const (p := q) (b := a)
    _ = p := PMF.bind_pure p

@[simp]
theorem independentCoupling_map_snd {α : Type uα} {β : Type uβ}
    (p : PMF α) (q : PMF β) :
    (independentCoupling p q).map Prod.snd = q := by
  rw [independentCoupling, PMF.map_bind]
  calc
    p.bind
          (fun a => (q.map fun b => (a, b)).map Prod.snd) =
        p.bind (fun _ => q) := by
          congr 1
          funext a
          rw [PMF.map_comp]
          simpa [Function.comp_def] using PMF.map_id q
    _ = q := PMF.bind_const p q

/-- Compose a coupling with related dependent probability kernels.

The result is the probabilistic analogue of relational composition for a
Kleisli bind.  Both output marginals are preserved exactly. -/
theorem RelCoupling.bind
    {α : Type uα} {β : Type uβ} {γ : Type*} {δ : Type*}
    {R : α → β → Prop} {S : γ → δ → Prop}
    {p : PMF α} {q : PMF β}
    {f : α → PMF γ} {g : β → PMF δ}
    (h : RelCoupling R p q)
    (hnext : ∀ a b, R a b → RelCoupling S (f a) (g b)) :
    RelCoupling S (p.bind f) (q.bind g) := by
  classical
  obtain ⟨outer, hfst, hsnd, hsupport⟩ := h
  let localCoupling : α × β → PMF (γ × δ) := fun pair =>
    if hpair : R pair.1 pair.2 then
      Classical.choose (hnext pair.1 pair.2 hpair)
    else
      independentCoupling (f pair.1) (g pair.2)
  have hlocal_fst (pair : α × β) :
      (localCoupling pair).map Prod.fst = f pair.1 := by
    by_cases hpair : R pair.1 pair.2
    · have hchosen :=
        Classical.choose_spec (hnext pair.1 pair.2 hpair)
      simpa only [localCoupling, dif_pos hpair] using hchosen.1
    · simp only [localCoupling, dif_neg hpair, independentCoupling_map_fst]
  have hlocal_snd (pair : α × β) :
      (localCoupling pair).map Prod.snd = g pair.2 := by
    by_cases hpair : R pair.1 pair.2
    · have hchosen :=
        Classical.choose_spec (hnext pair.1 pair.2 hpair)
      simpa only [localCoupling, dif_pos hpair] using hchosen.2.1
    · simp only [localCoupling, dif_neg hpair, independentCoupling_map_snd]
  refine ⟨outer.bind localCoupling, ?_, ?_, ?_⟩
  · rw [PMF.map_bind]
    calc
      outer.bind (fun pair => (localCoupling pair).map Prod.fst) =
          outer.bind (fun pair => f pair.1) := by
            congr 1
            funext pair
            exact hlocal_fst pair
      _ = (outer.map Prod.fst).bind f := by
        rw [PMF.bind_map]
        rfl
      _ = p.bind f := by rw [hfst]
  · rw [PMF.map_bind]
    calc
      outer.bind (fun pair => (localCoupling pair).map Prod.snd) =
          outer.bind (fun pair => g pair.2) := by
            congr 1
            funext pair
            exact hlocal_snd pair
      _ = (outer.map Prod.snd).bind g := by
        rw [PMF.bind_map]
        rfl
      _ = q.bind g := by rw [hsnd]
  · intro nextPair hnextPair
    obtain ⟨pair, hpairSupport, hnextSupport⟩ :=
      (PMF.mem_support_bind_iff outer localCoupling nextPair).mp hnextPair
    have hpair : R pair.1 pair.2 := hsupport pair hpairSupport
    have hchosen :=
      Classical.choose_spec (hnext pair.1 pair.2 hpair)
    apply hchosen.2.2 nextPair
    simpa only [localCoupling, dif_pos hpair] using hnextSupport

end PMF
