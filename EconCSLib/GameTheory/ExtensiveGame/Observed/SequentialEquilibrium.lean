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

/-- Structural hypotheses for the first finite sequential-equilibrium layer.

Player finiteness is a typeclass parameter. The finite-EFG certificate
supplies a bounded, locally finite history unfolding, finite information
carriers, representation of every declared information state, and mover
coherence. Chance is part of `ObservedChanceGame`; the recall certificate
proves perfect recall. Decidability of terminality is stored only because the
existing executable bounded stochastic semantics requires it. -/
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

namespace FiniteSequentialHypotheses

variable [Fintype N] [DecidableEq N]

/-- The stored recall certificate proves classic perfect recall. -/
theorem perfectRecall (h : G.FiniteSequentialHypotheses) :
    G.observed.PerfectRecall :=
  h.recallCertificate.perfectRecall

/-- The complete legal-history carrier is finite under the structural
finite-EFG certificate, even if the compact state carrier is infinite. -/
@[implicit_reducible]
noncomputable def finiteHistory
    (h : G.FiniteSequentialHypotheses) :
    Finite G.observed.base.History := by
  letI : Finite
      (G.observed.base.toArena.BoundedHistoryFrom
        G.observed.base.init h.finiteEFG.lengthBound) :=
    Arena.finiteBoundedHistoryFrom
      h.finiteEFG.finiteAction h.finiteEFG.lengthBound
  exact
    Finite.of_injective
      (fun history =>
        (⟨history,
          Arena.History.length_le_of_hasLengthBoundFrom
            h.finiteEFG.hasLengthBound history.2⟩ :
          G.observed.base.toArena.BoundedHistoryFrom
            G.observed.base.init h.finiteEFG.lengthBound))
      (by
        intro first second heq
        exact congrArg Subtype.val heq)

/-- Every information state has finitely many occurrence-sensitive decision
history witnesses. -/
@[implicit_reducible]
noncomputable def finiteDecisionInfoWitness
    (h : G.FiniteSequentialHypotheses)
    (i : N) (information : G.observed.InfoState i) :
    Finite (G.observed.DecisionInfoWitness i information) := by
  letI : Finite G.observed.base.History := finiteHistory G h
  exact
    Finite.of_injective
      (fun occurrence => occurrence.history)
      (by
        intro first second heq
        cases first
        cases second
        simp_all)

/-- Probability of reaching one occurrence-sensitive decision history under
a behavioral profile and the game's declared chance kernels. -/
noncomputable def reachWeight
    (h : G.FiniteSequentialHypotheses)
    (profile : G.observed.BehavioralProfile)
    {i : N} {information : G.observed.InfoState i}
    (occurrence : G.observed.DecisionInfoWitness i information) :
    ℝ≥0∞ := by
  letI :
      (state : G.observed.base.State) →
        Decidable (G.observed.base.isTerminal state) :=
    h.terminalDecidable
  exact
    (G.observed.base.toArena.stochasticHistoryPMFFrom
      (BehavioralProfile.toHistoryPolicy G profile)
      (Arena.HistoryFrom.nil
        G.observed.base.toArena G.observed.base.init)
      occurrence.history.2.length)
      occurrence.history

/-- Total reach weight of one information state. -/
noncomputable def informationReachWeight
    (h : G.FiniteSequentialHypotheses)
    (profile : G.observed.BehavioralProfile)
    (i : N) (information : G.observed.InfoState i) :
    ℝ≥0∞ :=
  ∑' occurrence,
    reachWeight G h profile
      (occurrence :
        G.observed.DecisionInfoWitness i information)

/-- The information state is reached with positive total probability by the
given behavioral profile. -/
def HasPositiveInformationReach
    (h : G.FiniteSequentialHypotheses)
    (profile : G.observed.BehavioralProfile)
    (i : N) (information : G.observed.InfoState i) : Prop :=
  informationReachWeight G h profile i information ≠ 0

/-- The finite information-set reach denominator is never infinite. -/
theorem informationReachWeight_ne_top
    (h : G.FiniteSequentialHypotheses)
    (profile : G.observed.BehavioralProfile)
    (i : N) (information : G.observed.InfoState i) :
    informationReachWeight G h profile i information ≠ ∞ := by
  letI : Finite
      (G.observed.DecisionInfoWitness i information) :=
    finiteDecisionInfoWitness G h i information
  letI : Fintype
      (G.observed.DecisionInfoWitness i information) :=
    Fintype.ofFinite _
  rw [informationReachWeight, tsum_fintype]
  exact ENNReal.sum_ne_top.2 fun occurrence _ =>
    PMF.apply_ne_top _ occurrence.history

/-- Bayes' rule at a positively reached information state, obtained by
normalizing the occurrence reach weights. -/
noncomputable def bayesBelief
    (h : G.FiniteSequentialHypotheses)
    (profile : G.observed.BehavioralProfile)
    (i : N) (information : G.observed.InfoState i)
    (hpositive :
      HasPositiveInformationReach G h profile i information) :
    PMF (G.observed.DecisionInfoWitness i information) :=
  PMF.normalize
    (fun occurrence => reachWeight G h profile occurrence)
    hpositive
    (informationReachWeight_ne_top G h profile i information)

/-- The finite Bayes belief is the node reach weight divided by the total
information-state reach weight. -/
@[simp]
theorem bayesBelief_apply
    (h : G.FiniteSequentialHypotheses)
    (profile : G.observed.BehavioralProfile)
    (i : N) (information : G.observed.InfoState i)
    (hpositive :
      HasPositiveInformationReach G h profile i information)
    (occurrence :
      G.observed.DecisionInfoWitness i information) :
    bayesBelief G h profile i information hpositive occurrence =
      reachWeight G h profile occurrence *
        (informationReachWeight G h profile i information)⁻¹ :=
  rfl

/-- Bayes-normalized beliefs have total mass one. -/
@[simp]
theorem bayesBelief_tsum
    (h : G.FiniteSequentialHypotheses)
    (profile : G.observed.BehavioralProfile)
    (i : N) (information : G.observed.InfoState i)
    (hpositive :
      HasPositiveInformationReach G h profile i information) :
    ∑' occurrence,
        bayesBelief G h profile i information hpositive occurrence =
      1 :=
  PMF.tsum_coe _

end FiniteSequentialHypotheses

namespace Assessment

variable [Fintype N] [DecidableEq N]

/-- Kreps--Wilson consistency witnessed by one common sequence of completely
mixed behavioral profiles.

The positivity field is explicit because full support of player behavior does
not turn a zero-probability chance branch into a positive-probability branch.
All convergence is pointwise convergence in Mathlib's topology on
`ℝ≥0∞`. -/
structure KrepsWilsonConsistencyCertificate
    (h : G.FiniteSequentialHypotheses)
    (assessment : G.Assessment) where
  /-- Common perturbation sequence. -/
  tremble : ℕ → G.observed.BehavioralProfile
  /-- Every perturbation puts positive mass on every player action. -/
  completelyMixed :
    ∀ n, BehavioralProfile.IsCompletelyMixed G (tremble n)
  /-- Every information set has a Bayes denominator along the perturbation
  sequence. -/
  positiveReach :
    ∀ (n : ℕ) (i : N)
      (information : G.observed.InfoState i),
      FiniteSequentialHypotheses.HasPositiveInformationReach
        G h (tremble n) i information
  /-- Perturbed behavior converges pointwise to limiting behavior. -/
  behaviorTendsTo :
    BehavioralProfile.TendsTo G tremble assessment.behavior
  /-- Bayes beliefs induced by the perturbations converge pointwise to the
  limiting belief system. -/
  beliefsTendTo :
    ∀ (i : N) (information : G.observed.InfoState i)
      (occurrence :
        G.observed.DecisionInfoWitness i information),
      Tendsto
        (fun n =>
          FiniteSequentialHypotheses.bayesBelief G h
            (tremble n) i information
            (positiveReach n i information)
            occurrence)
        atTop
        (𝓝 (assessment.beliefs i information occurrence))

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
    (i : N) (information : G.observed.InfoState i)
    (occurrence :
      G.observed.DecisionInfoWitness i information) :
    Tendsto
      (fun n =>
        FiniteSequentialHypotheses.bayesBelief G h
          (consistent.tremble n) i information
          (consistent.positiveReach n i information)
          occurrence)
      atTop
      (𝓝 (assessment.beliefs i information occurrence)) :=
  consistent.beliefsTendTo i information occurrence

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
      (i : N) → (information : G.observed.InfoState i) →
        PMF (G.observed.InfoAction i information) → ℝ

namespace Assessment

variable [Fintype N] [DecidableEq N]

/-- Evaluator-relative sequential rationality: at every information state,
the assessment's behavioral law weakly dominates every local behavioral
deviation according to the supplied continuation evaluator. -/
def IsSequentiallyRationalFor
    (assessment : G.Assessment)
    (evaluator : G.SequentialDecisionEvaluator) : Prop :=
  ∀ (i : N) (information : G.observed.InfoState i)
    (deviation : PMF (G.observed.InfoAction i information)),
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
