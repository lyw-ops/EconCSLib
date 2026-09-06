/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.FiniteUnfolding
import EconCSLib.GameTheory.ExtensiveGame.Observed.PerfectRecall
import Mathlib.Topology.Instances.Rat

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
open BigOperators

variable {N U : Type*} (G : ObservedChanceGame N U)

/-- Exact rational belief observables at every represented
decision-information coordinate. -/
abbrev RawBeliefSystem :=
  (i : N) → (information : G.observed.RepresentedInfo i) →
    (G.observed.DecisionInfoWitness i information.1 → ℚ) → ℚ

/-- A normalized belief over complete decision-history occurrences at every
represented information coordinate. -/
abbrev BeliefSystem :=
  (i : N) → (information : G.observed.RepresentedInfo i) →
    FiniteLaw (G.observed.DecisionInfoWitness i information.1)

namespace BeliefSystem

/-- Forget the sparse presentation and expose exact rational observables. -/
def toRaw (beliefs : G.BeliefSystem) : G.RawBeliefSystem :=
  fun i information value =>
    (beliefs i information).expectRat value

/-- Every information-state belief has total mass one. -/
@[simp]
theorem normalized_apply (beliefs : G.BeliefSystem)
    (i : N) (information : G.observed.RepresentedInfo i) :
    FiniteLaw.totalWeight (beliefs i information).atoms = 1 :=
  (beliefs i information).normalized

/-- Pointwise convergence of normalized beliefs on every complete
decision-history occurrence. -/
def TendsTo (sequence : ℕ → G.BeliefSystem)
    (limit : G.BeliefSystem) : Prop :=
  ∀ (i : N) (information : G.observed.RepresentedInfo i)
    (value : G.observed.DecisionInfoWitness i information.1 → ℚ),
    Tendsto
      (fun n => (sequence n i information).expectRat value)
      atTop
      (𝓝 ((limit i information).expectRat value))

end BeliefSystem

/-- A behavioral assessment: strategic behavior together with normalized
beliefs at every represented decision-information coordinate. -/
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
  ∀ (i : N) (information : G.observed.RepresentedInfo i)
    (action : G.observed.InfoAction i information.1),
    (profile i information).HasPositiveAtom action

/-- Pointwise convergence of every information-indexed action
probability. -/
def TendsTo
    (sequence : ℕ → G.observed.BehavioralProfile)
    (limit : G.observed.BehavioralProfile) : Prop :=
  ∀ (i : N) (information : G.observed.RepresentedInfo i)
    (value : G.observed.InfoAction i information.1 → ℚ),
    Tendsto
      (fun n => (sequence n i information).expectRat value)
      atTop
      (𝓝 ((limit i information).expectRat value))

end BehavioralProfile

/-- Structural hypotheses for the first finite sequential-equilibrium layer.

Player finiteness is a typeclass parameter. The finite-EFG certificate
supplies a bounded, locally finite history unfolding and finite represented
decision-information carriers. Chance is part of `ObservedChanceGame`; the
recall certificate proves perfect recall. Decidability of terminality is
stored only because the existing executable bounded stochastic semantics
requires it. -/
structure FiniteSequentialHypotheses
    [Fintype N] [DecidableEq N] where
  /-- Finite occurrence-sensitive observed-EFG presentation. -/
  finiteEFG : G.observed.FiniteEFGHypotheses
  /-- Factorized perfect-recall certificate. -/
  recallCertificate : G.observed.RecallCertificate
  /-- Executable terminal test used by bounded stochastic execution. -/
  terminalDecidable :
    (state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)
  /-- Explicit finite enumeration of legal complete histories. -/
  historyFintype : Fintype G.observed.base.History
  /-- Executable equality on legal complete histories. -/
  historyDecidableEq : DecidableEq G.observed.base.History
  /-- Explicit finite enumeration of every occurrence-sensitive information
  fiber. -/
  decisionInfoWitnessFintype :
    ∀ (i : N) (information : G.observed.RepresentedInfo i),
      Fintype (G.observed.DecisionInfoWitness i information.1)
  /-- Ordered executable enumeration used by finite sums and normalization. -/
  decisionInfoWitnessList :
    ∀ (i : N) (information : G.observed.RepresentedInfo i),
      List (G.observed.DecisionInfoWitness i information.1)
  /-- The executable enumeration covers every occurrence witness. -/
  decisionInfoWitnessList_complete :
    ∀ (i : N) (information : G.observed.RepresentedInfo i)
      (occurrence : G.observed.DecisionInfoWitness i information.1),
      occurrence ∈ decisionInfoWitnessList i information

namespace FiniteSequentialHypotheses

variable [Fintype N] [DecidableEq N]

/-- The stored recall certificate proves classic perfect recall. -/
theorem perfectRecall (h : G.FiniteSequentialHypotheses) :
    G.observed.PerfectRecall :=
  h.recallCertificate.perfectRecall

/-- The complete legal-history carrier is finite under the structural
finite-EFG certificate, even if the compact state carrier is infinite. -/
@[implicit_reducible]
def finiteHistory
    (h : G.FiniteSequentialHypotheses) :
    Finite G.observed.base.History := by
  letI : Fintype G.observed.base.History := h.historyFintype
  exact Finite.of_fintype _

/-- Every represented information coordinate has finitely many
occurrence-sensitive decision-history witnesses. -/
@[implicit_reducible]
def finiteDecisionInfoWitness
    (h : G.FiniteSequentialHypotheses)
    (i : N) (information : G.observed.RepresentedInfo i) :
    Finite (G.observed.DecisionInfoWitness i information.1) := by
  letI : Fintype
      (G.observed.DecisionInfoWitness i information.1) :=
    h.decisionInfoWitnessFintype i information
  exact Finite.of_fintype _

/-- Probability of reaching one occurrence-sensitive decision history under
a behavioral profile and the game's declared chance kernels. -/
def reachWeight
    (h : G.FiniteSequentialHypotheses)
    (profile : G.observed.BehavioralProfile)
    {i : N} {information : G.observed.RepresentedInfo i}
    (occurrence : G.observed.DecisionInfoWitness i information.1) :
    ℚ≥0 := by
  letI :
      (state : G.observed.base.State) →
        Decidable (G.observed.base.isTerminal state) :=
    h.terminalDecidable
  letI : DecidableEq G.observed.base.History :=
    h.historyDecidableEq
  exact
    (G.observed.base.toArena.stochasticHistoryLawFrom
      (BehavioralProfile.toHistoryPolicy G profile)
      (Arena.HistoryFrom.nil
        G.observed.base.toArena G.observed.base.init)
      occurrence.history.2.length).mass occurrence.history

/-- Total reach weight of one information state. -/
def informationReachWeight
    (h : G.FiniteSequentialHypotheses)
    (profile : G.observed.BehavioralProfile)
    (i : N) (information : G.observed.RepresentedInfo i) :
    ℚ≥0 :=
  (h.decisionInfoWitnessList i information |>.map fun occurrence =>
    reachWeight G h profile
      (occurrence :
        G.observed.DecisionInfoWitness i information.1)).sum

/-- The information state is reached with positive total probability by the
given behavioral profile. -/
def HasPositiveInformationReach
    (h : G.FiniteSequentialHypotheses)
    (profile : G.observed.BehavioralProfile)
    (i : N) (information : G.observed.RepresentedInfo i) : Prop :=
  informationReachWeight G h profile i information ≠ 0

/-- Bayes' rule at a positively reached information state, obtained by
normalizing the occurrence reach weights. -/
def bayesBelief
    (h : G.FiniteSequentialHypotheses)
    (profile : G.observed.BehavioralProfile)
    (i : N) (information : G.observed.RepresentedInfo i)
    (hpositive :
      HasPositiveInformationReach G h profile i information) :
    FiniteLaw (G.observed.DecisionInfoWitness i information.1) := by
  let weights :=
    h.decisionInfoWitnessList i information |>.map fun occurrence =>
      (occurrence,
        reachWeight G h profile
          (occurrence :
            G.observed.DecisionInfoWitness i information.1))
  apply FiniteLaw.normalize weights
  have htotal :
      FiniteLaw.totalWeight weights =
        informationReachWeight G h profile i information := by
    simp [weights, FiniteLaw.totalWeight, informationReachWeight,
      List.map_map, Function.comp_def]
  intro hzero
  apply hpositive
  rw [← htotal]
  exact hzero

/-- Bayes-normalized beliefs have total mass one. -/
@[simp]
theorem bayesBelief_normalized
    (h : G.FiniteSequentialHypotheses)
    (profile : G.observed.BehavioralProfile)
    (i : N) (information : G.observed.RepresentedInfo i)
    (hpositive :
      HasPositiveInformationReach G h profile i information) :
    FiniteLaw.totalWeight
      (bayesBelief G h profile i information hpositive).atoms = 1 :=
  (bayesBelief G h profile i information hpositive).normalized

end FiniteSequentialHypotheses

namespace Assessment

variable [Fintype N] [DecidableEq N]

/-- Kreps--Wilson consistency witnessed by one common sequence of completely
mixed behavioral profiles.

The positivity field is explicit because full support of player behavior does
not turn a zero-probability chance branch into a positive-probability branch.
All convergence is convergence of exact rational observables. -/
structure KrepsWilsonConsistencyCertificate
    (h : G.FiniteSequentialHypotheses)
    (assessment : G.Assessment) where
  /-- Common perturbation sequence. -/
  tremble : ℕ → G.observed.BehavioralProfile
  /-- Every perturbation puts positive mass on every player action. -/
  completelyMixed :
    ∀ n, BehavioralProfile.IsCompletelyMixed G (tremble n)
  /-- Every represented information coordinate has a Bayes denominator along
  the perturbation sequence. -/
  positiveReach :
    ∀ (n : ℕ) (i : N)
      (information : G.observed.RepresentedInfo i),
      FiniteSequentialHypotheses.HasPositiveInformationReach
        G h (tremble n) i information
  /-- Perturbed behavior converges pointwise to limiting behavior. -/
  behaviorTendsTo :
    BehavioralProfile.TendsTo G tremble assessment.behavior
  /-- Bayes beliefs induced by the perturbations converge pointwise to the
  limiting belief system. -/
  beliefsTendTo :
    ∀ (i : N) (information : G.observed.RepresentedInfo i)
      (value :
        G.observed.DecisionInfoWitness i information.1 → ℚ),
      Tendsto
        (fun n =>
          (FiniteSequentialHypotheses.bayesBelief G h
              (tremble n) i information
              (positiveReach n i information)).expectRat value)
        atTop
        (𝓝 ((assessment.beliefs i information).expectRat value))

/-- Propositional consistency of an assessment: a common completely mixed
perturbation certificate exists. -/
def IsKrepsWilsonConsistent
    (h : G.FiniteSequentialHypotheses)
    (assessment : G.Assessment) : Prop :=
  Nonempty (KrepsWilsonConsistencyCertificate G h assessment)

/-- A consistent assessment exposes the pointwise convergence of its
completely mixed behavioral perturbations. -/
theorem KrepsWilsonConsistencyCertificate.behavior_converges
    {h : G.FiniteSequentialHypotheses}
    {assessment : G.Assessment}
    (consistent :
      Assessment.KrepsWilsonConsistencyCertificate
        G h assessment) :
    BehavioralProfile.TendsTo
      G consistent.tremble assessment.behavior :=
  consistent.behaviorTendsTo

/-- A consistent assessment exposes pointwise convergence of every induced
Bayes belief. -/
theorem KrepsWilsonConsistencyCertificate.belief_converges
    {h : G.FiniteSequentialHypotheses}
    {assessment : G.Assessment}
    (consistent :
      Assessment.KrepsWilsonConsistencyCertificate
        G h assessment)
    (i : N) (information : G.observed.RepresentedInfo i)
    (value :
      G.observed.DecisionInfoWitness i information.1 → ℚ) :
    Tendsto
      (fun n =>
        (FiniteSequentialHypotheses.bayesBelief G h
            (consistent.tremble n) i information
            (consistent.positiveReach n i information)).expectRat value)
      atTop
      (𝓝 ((assessment.beliefs i information).expectRat value)) :=
  consistent.beliefsTendTo i information value

end Assessment

/-- A local continuation-value evaluator for a finite behavioral assessment.

The eventual canonical instance should condition expected terminal utility on
the assessment's occurrence beliefs and then execute continuation behavior.
Keeping the evaluator explicit prevents this foundation from claiming an
operational result before that bridge is proved. -/
structure SequentialDecisionEvaluator where
  /-- Value to the acting player of selecting one local behavioral law at the
  given information state under the supplied assessment. -/
  value :
    G.Assessment →
      (i : N) → (information : G.observed.RepresentedInfo i) →
        FiniteLaw (G.observed.InfoAction i information.1) → ℝ

namespace Assessment

variable [Fintype N] [DecidableEq N]

/-- Evaluator-relative sequential rationality: at every information state,
the assessment's behavioral law weakly dominates every local behavioral
deviation according to the supplied continuation evaluator. -/
def IsSequentiallyRationalFor
    (assessment : G.Assessment)
    (evaluator : G.SequentialDecisionEvaluator) : Prop :=
  ∀ (i : N) (information : G.observed.RepresentedInfo i)
    (deviation : FiniteLaw (G.observed.InfoAction i information.1)),
    evaluator.value assessment i information deviation ≤
      evaluator.value assessment i information
        (assessment.behavior i information)

/-- Evaluator-relative finite sequential equilibrium.

This predicate packages the correct consistency architecture with local
rationality, but remains explicitly evaluator-relative until conditional
continuation utility is installed. -/
def IsSequentialEquilibriumFor
    (assessment : G.Assessment)
    (h : G.FiniteSequentialHypotheses)
    (evaluator : G.SequentialDecisionEvaluator) : Prop :=
  Assessment.IsKrepsWilsonConsistent G h assessment ∧
    Assessment.IsSequentiallyRationalFor G assessment evaluator

/-- Evaluator-relative sequential equilibrium implies Kreps--Wilson
consistency. -/
theorem IsSequentialEquilibriumFor.consistent
    {assessment : G.Assessment}
    {h : G.FiniteSequentialHypotheses}
    {evaluator : G.SequentialDecisionEvaluator}
    (equilibrium :
      IsSequentialEquilibriumFor G assessment h evaluator) :
    Assessment.IsKrepsWilsonConsistent G h assessment :=
  equilibrium.1

/-- Evaluator-relative sequential equilibrium implies local sequential
rationality for the supplied evaluator. -/
theorem IsSequentialEquilibriumFor.sequentiallyRational
    {assessment : G.Assessment}
    {h : G.FiniteSequentialHypotheses}
    {evaluator : G.SequentialDecisionEvaluator}
    (equilibrium :
      IsSequentialEquilibriumFor G assessment h evaluator) :
    Assessment.IsSequentiallyRationalFor G assessment evaluator :=
  equilibrium.2

end Assessment

end ExtensiveGame.ObservedChanceGame
