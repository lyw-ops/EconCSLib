/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.FiniteUnfolding
import EconCSLib.GameTheory.ExtensiveGame.Observed.PerfectRecall
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Finite sequential-equilibrium foundations

This experimental module implements the probability and convergence
vocabulary needed by a finite Kreps--Wilson sequential-equilibrium
development:

* raw and normalized beliefs over occurrence-sensitive decision histories;
* assessments;
* finite Bayes normalization from behavioral reach weights;
* completely mixed behavioral profiles;
* consistency witnessed by a common sequence of completely mixed profiles;
* evaluator-relative local sequential rationality.

Belief points are `ObservedGame.DecisionInfoWitness` values, so two complete
histories that have the same endpoint state remain distinct. Bayes
normalization requires positive total information-set reach. Beliefs at an
off-path information set are instead constrained by convergence of Bayes
beliefs along the completely mixed perturbation sequence.

The final rationality predicate is deliberately parameterized by a local
continuation-value evaluator. Until that evaluator is instantiated by, and
proved equivalent to, conditional expected continuation utility, the
predicate `IsSequentialEquilibriumFor` below is not advertised as the
standard operational sequential-equilibrium solution concept and implies
neither Nash equilibrium nor SPE.

The assessment and consistency architecture follows Kreps and Wilson,
"Sequential Equilibria", *Econometrica* 50(4), 1982, pp. 863--894.
-/

namespace ExtensiveGame.ObservedChanceGame

open Filter Topology
open scoped ENNReal

variable {N U : Type*} (G : ObservedChanceGame N U)

/-- Nonnegative, not necessarily normalized belief weights at every declared
decision information state.

The finite model certificate used by Bayes normalization separately ensures
that every declared information state has a decision-history witness. -/
abbrev RawBeliefSystem :=
  (i : N) → (information : G.observed.InfoState i) →
    G.observed.DecisionInfoWitness i information → ℝ≥0∞

/-- A normalized belief over complete decision-history occurrences at every
declared information state. -/
abbrev BeliefSystem :=
  (i : N) → (information : G.observed.InfoState i) →
    PMF (G.observed.DecisionInfoWitness i information)

namespace BeliefSystem

/-- Forget the normalization certificate and expose the point weights of a
belief system. -/
def toRaw (beliefs : G.BeliefSystem) : G.RawBeliefSystem :=
  fun i information occurrence => beliefs i information occurrence

/-- Every information-state belief has total mass one. -/
@[simp]
theorem tsum_apply (beliefs : G.BeliefSystem)
    (i : N) (information : G.observed.InfoState i) :
    ∑' occurrence, beliefs i information occurrence = 1 :=
  PMF.tsum_coe (beliefs i information)

/-- Pointwise convergence of normalized beliefs on every complete
decision-history occurrence. -/
def TendsTo (sequence : ℕ → G.BeliefSystem)
    (limit : G.BeliefSystem) : Prop :=
  ∀ (i : N) (information : G.observed.InfoState i)
    (occurrence : G.observed.DecisionInfoWitness i information),
    Tendsto
      (fun n => sequence n i information occurrence)
      atTop
      (𝓝 (limit i information occurrence))

end BeliefSystem

/-- A behavioral assessment: strategic behavior together with normalized
beliefs at every decision information state. -/
structure Assessment where
  /-- Information-indexed behavioral profile. -/
  behavior : G.observed.BehavioralProfile
  /-- Normalized beliefs over the complete histories in each information
  state. -/
  beliefs : G.BeliefSystem

namespace BehavioralProfile

/-- A behavioral profile is completely mixed when every abstract action at
every declared decision information state has positive mass. -/
def IsCompletelyMixed
    (profile : G.observed.BehavioralProfile) : Prop :=
  ∀ (i : N) (information : G.observed.InfoState i)
    (action : G.observed.InfoAction i information),
    0 < profile i information action

/-- Pointwise convergence of every information-indexed action
probability. -/
def TendsTo
    (sequence : ℕ → G.observed.BehavioralProfile)
    (limit : G.observed.BehavioralProfile) : Prop :=
  ∀ (i : N) (information : G.observed.InfoState i)
    (action : G.observed.InfoAction i information),
    Tendsto
      (fun n => sequence n i information action)
      atTop
      (𝓝 (limit i information action))

end BehavioralProfile

end ExtensiveGame.ObservedChanceGame
