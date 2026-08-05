/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Continuation
import EconCSLib.GameTheory.ExtensiveGame.Observed.Mixed
import EconCSLib.GameTheory.ExtensiveGame.Observed.PerfectRecall
import EconCSLib.GameTheory.ExtensiveGame.Observed.WellFormed

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.Kuhn

Realization certificates between mixed contingent plans and behavioral
strategies.

Kuhn's theorem is a realization theorem, not generally a strict isomorphism of
strategy spaces.  This module makes that distinction structural.  A
root-scoped certificate supplies:

* a playerwise map from mixed plans to behavioral strategies;
* equality of the complete bounded payoff law at the selected root;
* exact realization of every unilateral behavioral deviation by a mixed
  deviation.

These fields induce a `LawGameForm.Hom` with semantic deviation completeness,
and therefore give two-way Nash transfer without claiming strategy
surjectivity.

A second, deliberately stronger continuation-wide certificate requires one
global behavioralization map to satisfy the same equations at every
continuation root.  It induces a `ContinuationGameForm.Hom` and bounded Nash on presentation-designated continuations
transfer.  Perfect recall alone should not be used to construct this stronger
certificate for arbitrary mixed profiles: ex-ante correlations between a
player's choices can make root-scoped conditioning depend on the continuation.

`FiniteKuhnHypotheses` records the assumptions used by the constructive
root-scoped theorem in `KuhnConditioning`: perfect recall and finitely
many decision information states per player.

`FiniteInformationHypotheses` records exactly what is needed to construct the
independent complete-plan law and prove its local marginals.
`FiniteNoAbsentMindednessHypotheses` adds the no-repeated-decision-key property
needed only when that pre-sampled law is compared with repeated local
behavioral execution.

## Main definitions

* `ObservedGame.FiniteKuhnHypotheses`.
* `ObservedGame.FiniteInformationHypotheses`.
* `ObservedGame.FiniteNoAbsentMindednessHypotheses`.
* `ObservedGame.BehavioralStrategy.toMixed`.
* `ObservedChanceGame.mixedContinuationFamilyOnRoots`.
* `ObservedChanceGame.MixedBehavioralRealizationAt`.
* `ObservedChanceGame.MixedBehavioralContinuationRealization`.

## Main results

* `MixedBehavioralRealizationAt.lawHom`.
* `MixedBehavioralRealizationAt.isNash_iff`.
* `MixedBehavioralContinuationRealization.continuationHom`.
* `MixedBehavioralContinuationRealization.isNashOnRootsAtFuel_iff`.

The concrete conditional construction and the resulting unconditional
bounded Kuhn Nash-on-designated-continuations theorems are in `KuhnConditioning`.

## Source boundary

The finite perfect-recall realization target is [Kuhn 1953, §4, Thm. 4] and
[MFoGT, Thm. 6.3.4]. The Lean certificates below use discrete `PMF` laws and
terminal-aware bounded complete-history execution. Root-scoped conditioning,
deviation-complete law morphisms, and continuation-family transport are
EconCSLib representation theorems; the citations do not justify an
arbitrary-measure or infinite-path equivalence.
-/

namespace ExtensiveGame.ObservedGame

variable {N U : Type*}

/-- Standard finiteness and recall hypotheses for the constructive,
root-scoped Kuhn realization theorem proved in `KuhnConditioning`.

Keeping the hypotheses separate from the realization certificate lets the
base API state generic transfer theorems without baking in one particular
conditionalization construction. -/
structure FiniteKuhnHypotheses
    (G : ObservedGame N U) [DecidableEq N] : Prop where
  /-- Players remember their own prior information states and actions. -/
  perfectRecall : G.PerfectRecall
  /-- Every player has finitely many decision information states. -/
  finiteInfoState :
    ∀ i : N, Finite (G.InfoState i)

/-- The exact hypotheses needed to pre-sample a behavioral profile as
independent complete contingent plans and prove their local action marginals.

No player equality or recall property is needed at this construction layer. -/
structure FiniteInformationHypotheses
    (G : ObservedGame N U) : Prop where
  /-- Every player has finitely many decision information states. -/
  finiteInfoState :
    ∀ i : N, Finite (G.InfoState i)

/-- The exact structural hypotheses needed to identify pre-sampled complete
plans with repeated local behavioral execution.

Unlike `FiniteKuhnHypotheses`, this does not require perfect recall.  It
requires only the no-repeated-decision-key property consumed by deferred
sampling, together with finite decision-information types. -/
structure FiniteNoAbsentMindednessHypotheses
    (G : ObservedGame N U) [DecidableEq N] : Prop where
  /-- No player revisits one decision information state along a history. -/
  noAbsentMindedness : G.NoAbsentMindedness
  /-- Every player has finitely many decision information states. -/
  finiteInfoState :
    ∀ i : N, Finite (G.InfoState i)

namespace FiniteEFGHypotheses

variable {G : ObservedGame N U}

/-- The structural finite-EFG certificate supplies the finite-information
hypothesis needed for independent complete-plan sampling. -/
def toFiniteInformationHypotheses
    (h : G.FiniteEFGHypotheses) :
    G.FiniteInformationHypotheses where
  finiteInfoState := h.finiteInfoState

/-- Adding perfect recall to a structural finite-EFG certificate supplies the
standard hypotheses for root-scoped constructive Kuhn realization. -/
def toFiniteKuhnHypotheses
    [DecidableEq N]
    (h : G.FiniteEFGHypotheses)
    (hPerfectRecall : G.PerfectRecall) :
    G.FiniteKuhnHypotheses where
  perfectRecall := hPerfectRecall
  finiteInfoState := h.finiteInfoState

end FiniteEFGHypotheses

namespace BehavioralStrategy

variable (G : ObservedGame N U)

/-- Independently sample one abstract action at every decision information
state to obtain a law on complete pure contingent plans.

This construction is the behavioral-to-mixed half of the finite Kuhn bridge.
Perfect recall is not needed for the construction or its local marginals; it
is not needed for the execution comparison either: no-absent-mindedness is the
strictly weaker property consumed there. -/
noncomputable def toMixed {i : N}
    [Fintype (G.InfoState i)]
    (strategy : G.BehavioralStrategy i) :
    G.MixedStrategy i := by
  change
    (information : G.InfoState i) →
      PMF (G.InfoAction i information) at strategy
  change
    PMF
      ((information : G.InfoState i) →
        G.InfoAction i information)
  exact PMF.fintypePi strategy

/-- The sampled pure plan has exactly the declared behavioral action law at
each information state. -/
theorem toMixed_actionMarginal {i : N}
    [Fintype (G.InfoState i)]
    (strategy : G.BehavioralStrategy i)
    (information : G.InfoState i) :
    (toMixed G strategy).map
        (fun pureStrategy =>
          pureStrategy information) =
      strategy information := by
  change
    (information : G.InfoState i) →
      PMF (G.InfoAction i information) at strategy
  change
    (PMF.fintypePi strategy).map
        (fun pureStrategy =>
          pureStrategy information) =
      strategy information
  exact PMF.fintypePi_map_apply
    strategy information

end BehavioralStrategy

namespace FiniteInformationHypotheses

variable {G : ObservedGame N U}

/-- Behavioral-to-mixed construction under finite information only. -/
noncomputable def behavioralToMixedStrategy
    (h : G.FiniteInformationHypotheses)
    (i : N)
    (strategy : G.BehavioralStrategy i) :
    G.MixedStrategy i :=
  letI : Finite (G.InfoState i) :=
    h.finiteInfoState i
  letI : Fintype (G.InfoState i) :=
    Fintype.ofFinite (G.InfoState i)
  strategy.toMixed G

/-- Independently pre-sample every player's complete contingent plan. -/
noncomputable def behavioralToMixedProfile
    (h : G.FiniteInformationHypotheses)
    (profile : G.BehavioralProfile) :
    G.MixedProfile :=
  fun i =>
    h.behavioralToMixedStrategy i (profile i)

/-- Every local action marginal of the weak-hypothesis construction is the
declared behavioral law. -/
theorem behavioralToMixedStrategy_actionMarginal
    (h : G.FiniteInformationHypotheses)
    (i : N)
    (strategy : G.BehavioralStrategy i)
    (information : G.InfoState i) :
    (h.behavioralToMixedStrategy i strategy).map
        (fun pureStrategy => pureStrategy information) =
      strategy information := by
  letI : Finite (G.InfoState i) :=
    h.finiteInfoState i
  letI : Fintype (G.InfoState i) :=
    Fintype.ofFinite (G.InfoState i)
  exact
    BehavioralStrategy.toMixed_actionMarginal
      G strategy information

/-! The concrete-history forms below still consume only finite information:
`actionAt` merely realizes the already-sampled abstract action through the
game's indexed action equivalence. -/

/-- At a concrete player history, the action prescribed by the sampled pure
plan has exactly the source behavioral concrete-action law. -/
theorem behavioralToMixedStrategy_actionLawAt
    (h : G.FiniteInformationHypotheses)
    (i : N)
    (strategy : G.BehavioralStrategy i)
    (history :
      G.base.toArena.HistoryFrom G.base.init)
    (hmover :
      G.base.mover history.1 = some i)
    (hnonterminal :
      ¬ G.base.isTerminal history.1) :
    (h.behavioralToMixedStrategy
      i strategy).map
        (fun pureStrategy =>
          pureStrategy.actionAt
            G history hmover hnonterminal) =
      strategy.actionLawAt
        G history hmover hnonterminal := by
  unfold PureStrategy.actionAt
    BehavioralStrategy.actionLawAt
  calc
    (h.behavioralToMixedStrategy
        i strategy).map
          (fun pureStrategy =>
            G.actionEquiv history i hmover hnonterminal
              (pureStrategy
                (G.infoAt history i hmover hnonterminal))) =
        ((h.behavioralToMixedStrategy
            i strategy).map
              (fun pureStrategy =>
                pureStrategy
                  (G.infoAt history i hmover hnonterminal))).map
            (G.actionEquiv history i hmover hnonterminal) := by
      exact
        (PMF.map_comp
          (fun pureStrategy =>
            pureStrategy
              (G.infoAt history i hmover hnonterminal))
          (h.behavioralToMixedStrategy
            i strategy)
          (G.actionEquiv history i hmover hnonterminal)).symm
    _ = (strategy
          (G.infoAt history i hmover hnonterminal)).map
            (G.actionEquiv history i hmover hnonterminal) := by
      exact congrArg
        (fun law :
          PMF
            (G.InfoAction i
              (G.infoAt history i hmover hnonterminal)) =>
          law.map
            (G.actionEquiv history i hmover hnonterminal))
        (h.behavioralToMixedStrategy_actionMarginal
          i strategy
          (G.infoAt history i hmover hnonterminal))

/-- The independently sampled complete pure profile has the same current
concrete-action marginal as the source behavioral profile. -/
theorem behavioralToMixedProfile_actionLawAt
    [Fintype N]
    (h : G.FiniteInformationHypotheses)
    (profile : G.BehavioralProfile)
    (history :
      G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hmover :
      G.base.mover history.1 = some i)
    (hnonterminal :
      ¬ G.base.isTerminal history.1) :
    ((h.behavioralToMixedProfile
        profile).pureProfileLaw G).map
        (fun pureProfile =>
          pureProfile.actionAt
            G history i hmover hnonterminal) =
      profile.actionLawAt
        G history i hmover hnonterminal := by
  unfold MixedProfile.pureProfileLaw
  calc
    (PMF.fintypePi
        (h.behavioralToMixedProfile profile)).map
          (fun pureProfile =>
            PureProfile.actionAt
              G pureProfile history i hmover hnonterminal) =
        ((PMF.fintypePi
          (h.behavioralToMixedProfile profile)).map
            (fun pureProfile =>
              pureProfile i)).map
          (fun pureStrategy =>
            PureStrategy.actionAt
              G pureStrategy history hmover hnonterminal) := by
      exact
        (PMF.map_comp
          (fun pureProfile => pureProfile i)
          (PMF.fintypePi
            (h.behavioralToMixedProfile profile))
          (fun pureStrategy =>
            PureStrategy.actionAt
              G pureStrategy history hmover hnonterminal)).symm
    _ = (h.behavioralToMixedStrategy
          i (profile i)).map
            (fun pureStrategy =>
              PureStrategy.actionAt
                G pureStrategy history hmover hnonterminal) := by
      rw [PMF.fintypePi_map_apply]
      rfl
    _ = profile.actionLawAt
          G history i hmover hnonterminal :=
      h.behavioralToMixedStrategy_actionLawAt
        i (profile i) history hmover hnonterminal

end FiniteInformationHypotheses

namespace FiniteNoAbsentMindednessHypotheses

variable {G : ObservedGame N U} [DecidableEq N]

/-- Forget no-absent-mindedness and retain exactly the finite-information
construction hypotheses. -/
def toFiniteInformationHypotheses
    (h : G.FiniteNoAbsentMindednessHypotheses) :
    G.FiniteInformationHypotheses where
  finiteInfoState := h.finiteInfoState

/-- Compatibility wrapper for the finite-information construction. -/
noncomputable def behavioralToMixedStrategy
    (h : G.FiniteNoAbsentMindednessHypotheses)
    (i : N)
    (strategy : G.BehavioralStrategy i) :
    G.MixedStrategy i :=
  h.toFiniteInformationHypotheses.behavioralToMixedStrategy i strategy

/-- Compatibility wrapper for independently sampled complete profiles. -/
noncomputable def behavioralToMixedProfile
    (h : G.FiniteNoAbsentMindednessHypotheses)
    (profile : G.BehavioralProfile) :
    G.MixedProfile :=
  h.toFiniteInformationHypotheses.behavioralToMixedProfile profile

/-- Compatibility wrapper for the abstract local marginal theorem. -/
theorem behavioralToMixedStrategy_actionMarginal
    (h : G.FiniteNoAbsentMindednessHypotheses)
    (i : N)
    (strategy : G.BehavioralStrategy i)
    (information : G.InfoState i) :
    (h.behavioralToMixedStrategy i strategy).map
        (fun pureStrategy => pureStrategy information) =
      strategy information :=
  h.toFiniteInformationHypotheses.behavioralToMixedStrategy_actionMarginal
    i strategy information

/-- Compatibility wrapper for the concrete local action-law theorem. -/
theorem behavioralToMixedStrategy_actionLawAt
    (h : G.FiniteNoAbsentMindednessHypotheses)
    (i : N)
    (strategy : G.BehavioralStrategy i)
    (history :
      G.base.toArena.HistoryFrom G.base.init)
    (hmover :
      G.base.mover history.1 = some i)
    (hnonterminal :
      ¬ G.base.isTerminal history.1) :
    (h.behavioralToMixedStrategy i strategy).map
        (fun pureStrategy =>
          pureStrategy.actionAt G history hmover hnonterminal) =
      strategy.actionLawAt G history hmover hnonterminal :=
  h.toFiniteInformationHypotheses.behavioralToMixedStrategy_actionLawAt
    i strategy history hmover hnonterminal

/-- Compatibility wrapper for the complete-profile concrete marginal. -/
theorem behavioralToMixedProfile_actionLawAt
    [Fintype N]
    (h : G.FiniteNoAbsentMindednessHypotheses)
    (profile : G.BehavioralProfile)
    (history :
      G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hmover :
      G.base.mover history.1 = some i)
    (hnonterminal :
      ¬ G.base.isTerminal history.1) :
    ((h.behavioralToMixedProfile profile).pureProfileLaw G).map
        (fun pureProfile =>
          pureProfile.actionAt G history i hmover hnonterminal) =
      profile.actionLawAt G history i hmover hnonterminal :=
  h.toFiniteInformationHypotheses.behavioralToMixedProfile_actionLawAt
    profile history i hmover hnonterminal

end FiniteNoAbsentMindednessHypotheses

namespace FiniteKuhnHypotheses

variable {G : ObservedGame N U} [DecidableEq N]

/-- Forget recall and retain exactly the finite-information construction
hypotheses. -/
def toFiniteInformationHypotheses
    (h : G.FiniteKuhnHypotheses) :
    G.FiniteInformationHypotheses where
  finiteInfoState := h.finiteInfoState

/-- The perfect-recall component supplies the no-repeated-information-key
condition needed by the pre-sampled execution proof. -/
theorem noAbsentMindedness
    (h : G.FiniteKuhnHypotheses) :
    G.NoAbsentMindedness :=
  h.perfectRecall.noAbsentMindedness

/-- Forget perfect recall and retain exactly the assumptions required for the
behavioral-to-mixed deferred-sampling direction. -/
def toFiniteNoAbsentMindednessHypotheses
    (h : G.FiniteKuhnHypotheses) :
    G.FiniteNoAbsentMindednessHypotheses where
  noAbsentMindedness := h.noAbsentMindedness
  finiteInfoState := h.finiteInfoState

/-- Behavioral-to-mixed construction using the finite-information witness
stored in the Kuhn hypotheses.

This is a compatibility wrapper around the weaker
`FiniteNoAbsentMindednessHypotheses` construction. -/
noncomputable def behavioralToMixedStrategy
    (h : G.FiniteKuhnHypotheses)
    (i : N)
    (strategy : G.BehavioralStrategy i) :
    G.MixedStrategy i :=
  h.toFiniteNoAbsentMindednessHypotheses.behavioralToMixedStrategy
    i strategy

/-- Map a complete behavioral profile to independent laws on each player's
complete contingent plans.

This is a compatibility wrapper around the weaker
`FiniteNoAbsentMindednessHypotheses` construction. -/
noncomputable def behavioralToMixedProfile
    (h : G.FiniteKuhnHypotheses)
    (profile : G.BehavioralProfile) :
    G.MixedProfile :=
  h.toFiniteNoAbsentMindednessHypotheses.behavioralToMixedProfile
    profile

/-- Every local action marginal of the constructed mixed plan is the source
behavioral law. -/
theorem behavioralToMixedStrategy_actionMarginal
    (h : G.FiniteKuhnHypotheses)
    (i : N)
    (strategy : G.BehavioralStrategy i)
    (information : G.InfoState i) :
    (h.behavioralToMixedStrategy
      i strategy).map
        (fun pureStrategy =>
          pureStrategy information) =
      strategy information := by
  exact
    FiniteNoAbsentMindednessHypotheses.behavioralToMixedStrategy_actionMarginal
      h.toFiniteNoAbsentMindednessHypotheses
      i strategy information

/-- At a concrete player history, the action prescribed by the sampled pure
plan has exactly the source behavioral concrete-action law. -/
theorem behavioralToMixedStrategy_actionLawAt
    (h : G.FiniteKuhnHypotheses)
    (i : N)
    (strategy : G.BehavioralStrategy i)
    (history :
      G.base.toArena.HistoryFrom G.base.init)
    (hmover :
      G.base.mover history.1 = some i)
    (hnonterminal :
      ¬ G.base.isTerminal history.1) :
    (h.behavioralToMixedStrategy
      i strategy).map
        (fun pureStrategy =>
          pureStrategy.actionAt
            G history hmover hnonterminal) =
      strategy.actionLawAt
        G history hmover hnonterminal :=
  FiniteNoAbsentMindednessHypotheses.behavioralToMixedStrategy_actionLawAt
    h.toFiniteNoAbsentMindednessHypotheses
    i strategy history hmover hnonterminal

/-- The independently sampled complete pure profile has the same current
concrete-action marginal as the source behavioral profile. -/
theorem behavioralToMixedProfile_actionLawAt
    [Fintype N]
    (h : G.FiniteKuhnHypotheses)
    (profile : G.BehavioralProfile)
    (history :
      G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hmover :
      G.base.mover history.1 = some i)
    (hnonterminal :
      ¬ G.base.isTerminal history.1) :
    ((h.behavioralToMixedProfile
        profile).pureProfileLaw G).map
        (fun pureProfile =>
          pureProfile.actionAt
            G history i hmover hnonterminal) =
      profile.actionLawAt
        G history i hmover hnonterminal :=
  FiniteNoAbsentMindednessHypotheses.behavioralToMixedProfile_actionLawAt
    h.toFiniteNoAbsentMindednessHypotheses
    profile history i hmover hnonterminal

end FiniteKuhnHypotheses

end ExtensiveGame.ObservedGame

namespace ExtensiveGame.ObservedChanceGame

universe uV

variable {N U : Type*}

/-- Bounded mixed contingent-plan continuations on a separately supplied root
presentation. -/
noncomputable def mixedContinuationFamilyOnRoots
    (G : ObservedChanceGame N U)
    [Fintype N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (roots : G.observed.RootPresentation)
    (fuel : ℕ) :
    ContinuationGameForm N where
  Strategy := G.observed.MixedStrategy
  Root :=
    G.observed.base.toArena.HistoryFrom
      G.observed.base.init
  IsDeclaredRoot := roots.IsRoot
  Outcome := PMF (Option (N → U))
  outcome := fun current profile =>
    G.mixedStoppedPayoffLawFrom profile current fuel

/-- Fixing a root in the mixed continuation family recovers the deterministic
view of the mixed law game form definitionally. -/
theorem mixedContinuationFamilyOnRoots_toGameForm
    (G : ObservedChanceGame N U)
    [Fintype N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (roots : G.observed.RootPresentation)
    (fuel : ℕ)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init) :
    (G.mixedContinuationFamilyOnRoots
      roots fuel).toGameForm current =
      (G.mixedLawGameForm current fuel).toGameForm :=
  rfl

/-- Bounded mixed Nash on presentation-designated continuations is exactly Nash on presentation-designated continuations in the representation-neutral mixed
continuation family. -/
theorem isMixedNashOnRootsAtFuel_iff_continuationFamily
    (G : ObservedChanceGame N U)
    [Fintype N] [DecidableEq N] [Preorder V]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (roots : G.observed.RootPresentation)
    (utility :
      PMF (Option (N → U)) → N → V)
    (profile : G.observed.MixedProfile)
    (fuel : ℕ) :
    G.IsMixedNashOnRootsAtFuel
        roots utility profile fuel ↔
      (G.mixedContinuationFamilyOnRoots
        roots fuel).IsNashOnRoots
          (fun _ => utility) profile :=
  Iff.rfl

/-! ### Root-scoped realization -/

/-- Exact strategic realization of mixed contingent plans by behavioral
strategies at one bounded continuation.

The deviation field is semantic rather than syntactic: every behavioral
deviation must have the same payoff law as some mixed deviation, but the
behavioral strategy itself need not lie in the image of `behavioralize`. -/
structure MixedBehavioralRealizationAt
    (G : ObservedChanceGame N U)
    [Fintype N] [DecidableEq N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init)
    (fuel : ℕ) where
  /-- Convert each player's mixed plan to a behavioral strategy. -/
  behavioralize :
    (i : N) →
      G.observed.MixedStrategy i →
        G.observed.BehavioralStrategy i
  /-- The mapped complete profile has exactly the source payoff law. -/
  map_payoffLaw :
    ∀ profile : G.observed.MixedProfile,
      G.behavioralStoppedPayoffLawFrom
          (fun i => behavioralize i (profile i))
          current fuel =
        G.mixedStoppedPayoffLawFrom
          profile current fuel
  /-- Every unilateral behavioral deviation is exactly realized by a mixed
  deviation in the same opponents' context. -/
  realize_deviation :
    ∀ (profile : G.observed.MixedProfile)
      (i : N)
      (targetStrategy :
        G.observed.BehavioralStrategy i),
      ∃ sourceStrategy :
          G.observed.MixedStrategy i,
        G.behavioralStoppedPayoffLawFrom
            (Function.update
              (fun j => behavioralize j (profile j))
              i targetStrategy)
            current fuel =
          G.mixedStoppedPayoffLawFrom
            (Function.update profile i sourceStrategy)
            current fuel

namespace MixedBehavioralRealizationAt

variable
    {G : ObservedChanceGame N U}
    [Fintype N] [DecidableEq N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    {current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init}
    {fuel : ℕ}

/-- Map a complete mixed profile through a root-scoped realization. -/
noncomputable def mapProfile
    (R : G.MixedBehavioralRealizationAt current fuel)
    (profile : G.observed.MixedProfile) :
    G.observed.BehavioralProfile :=
  fun i => R.behavioralize i (profile i)

@[simp]
theorem mapProfile_apply
    (R : G.MixedBehavioralRealizationAt current fuel)
    (profile : G.observed.MixedProfile)
    (i : N) :
    R.mapProfile profile i =
      R.behavioralize i (profile i) :=
  rfl

/-- The root-scoped certificate induces a law-game morphism from mixed plans
to behavioral strategies. -/
noncomputable def lawHom
    (R : G.MixedBehavioralRealizationAt current fuel) :
    (G.mixedLawGameForm current fuel).Hom
      (G.behavioralLawGameForm current fuel) where
  strategyMap :=
    R.behavioralize
  outcomeMap :=
    id
  map_outcomeLaw := by
    intro profile
    unfold LawGameForm.RealizesVia
    change
      (G.mixedStoppedPayoffLawFrom
        profile current fuel).map id =
        G.behavioralStoppedPayoffLawFrom
          (R.mapProfile profile) current fuel
    rw [PMF.map_id]
    exact (R.map_payoffLaw profile).symm

/-- The induced law morphism uses the certificate's profile map. -/
@[simp]
theorem lawHom_mapProfile
    (R : G.MixedBehavioralRealizationAt current fuel)
    (profile : G.observed.MixedProfile) :
    R.lawHom.mapProfile profile =
      R.mapProfile profile :=
  rfl

/-- The root-scoped realization gives exact semantic coverage of all
behavioral deviation laws. -/
theorem lawHom_outcomeDeviationCompleteAt
    (R : G.MixedBehavioralRealizationAt current fuel)
    (profile : G.observed.MixedProfile) :
    R.lawHom.OutcomeDeviationCompleteAt
      profile := by
  intro i targetStrategy
  obtain ⟨sourceStrategy, hrealizes⟩ :=
    R.realize_deviation
      profile i targetStrategy
  refine ⟨sourceStrategy, ?_⟩
  change
    G.behavioralStoppedPayoffLawFrom
        (Function.update
          (R.mapProfile profile)
          i targetStrategy)
        current fuel =
      (G.mixedStoppedPayoffLawFrom
        (Function.update profile i sourceStrategy)
        current fuel).map id
  rw [PMF.map_id]
  exact hrealizes

/-- Root-scoped realization preserves and reflects Nash equilibrium for every
functional on the complete payoff law. -/
theorem isNash_iff
    [Preorder V]
    (R : G.MixedBehavioralRealizationAt current fuel)
    (utility :
      PMF (Option (N → U)) → N → V)
    (profile : G.observed.MixedProfile) :
    (G.mixedLawGameForm current fuel).IsNash
        utility profile ↔
      (G.behavioralLawGameForm current fuel).IsNash
        utility (R.mapProfile profile) := by
  apply
    R.lawHom.isNash_iff_of_outcomeDeviationCompleteAt
      (profile := profile)
  · intro law i
    change utility (law.map id) i = utility law i
    rw [PMF.map_id]
  · exact
      R.lawHom_outcomeDeviationCompleteAt
        profile

end MixedBehavioralRealizationAt

/-! ### Continuation-wide realization -/

/-- A single mixed-to-behavioral strategy map that realizes complete laws and
all unilateral deviations at every continuation root.

This is intentionally stronger than a root-scoped Kuhn certificate.  Supplying
it is sufficient for Nash on presentation-designated continuations transfer; `FiniteKuhnHypotheses` alone is not claimed
to imply it for arbitrary mixed profiles. -/
structure MixedBehavioralContinuationRealization
    (G : ObservedChanceGame N U)
    [Fintype N] [DecidableEq N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    (fuel : ℕ) where
  /-- One root-independent behavioralization map for complete strategies. -/
  behavioralize :
    (i : N) →
      G.observed.MixedStrategy i →
        G.observed.BehavioralStrategy i
  /-- Exact payoff-law realization at every continuation. -/
  map_payoffLaw :
    ∀ (profile : G.observed.MixedProfile)
      (current :
        G.observed.base.toArena.HistoryFrom
          G.observed.base.init),
      G.behavioralStoppedPayoffLawFrom
          (fun i => behavioralize i (profile i))
          current fuel =
        G.mixedStoppedPayoffLawFrom
          profile current fuel
  /-- Exact deviation realization at every continuation. -/
  realize_deviation :
    ∀ (profile : G.observed.MixedProfile)
      (current :
        G.observed.base.toArena.HistoryFrom
          G.observed.base.init)
      (i : N)
      (targetStrategy :
        G.observed.BehavioralStrategy i),
      ∃ sourceStrategy :
          G.observed.MixedStrategy i,
        G.behavioralStoppedPayoffLawFrom
            (Function.update
              (fun j => behavioralize j (profile j))
              i targetStrategy)
            current fuel =
          G.mixedStoppedPayoffLawFrom
            (Function.update profile i sourceStrategy)
            current fuel

namespace MixedBehavioralContinuationRealization

variable
    {G : ObservedChanceGame N U}
    [Fintype N] [DecidableEq N]
    [(state : G.observed.base.State) →
      Decidable
        (G.observed.base.isTerminal state)]
    {fuel : ℕ}

/-- Map a complete mixed profile through a continuation-wide realization. -/
noncomputable def mapProfile
    (R : G.MixedBehavioralContinuationRealization fuel)
    (profile : G.observed.MixedProfile) :
    G.observed.BehavioralProfile :=
  fun i => R.behavioralize i (profile i)

/-- Restrict a continuation-wide realization to one root. -/
noncomputable def atRoot
    (R : G.MixedBehavioralContinuationRealization fuel)
    (current :
      G.observed.base.toArena.HistoryFrom
        G.observed.base.init) :
    G.MixedBehavioralRealizationAt
      current fuel where
  behavioralize :=
    R.behavioralize
  map_payoffLaw :=
    fun profile =>
      R.map_payoffLaw profile current
  realize_deviation :=
    fun profile i targetStrategy =>
      R.realize_deviation
        profile current i targetStrategy

/-- A continuation-wide realization induces a representation-neutral
continuation morphism. -/
noncomputable def continuationHom
    (R : G.MixedBehavioralContinuationRealization fuel)
    (roots : G.observed.RootPresentation) :
    (G.mixedContinuationFamilyOnRoots roots fuel).Hom
      (G.behavioralContinuationFamilyOnRoots roots fuel) where
  rootMap := id
  strategyMap :=
    R.behavioralize
  outcomeMap := id
  map_declaredRoot := by
    intro current hroot
    exact hroot
  map_outcome := by
    intro current profile
    change
      G.mixedStoppedPayoffLawFrom
          profile current fuel =
        G.behavioralStoppedPayoffLawFrom
          (R.mapProfile profile) current fuel
    exact (R.map_payoffLaw profile current).symm

/-- The identity root map covers every target declared root. -/
theorem continuationHom_declaredRootSurjective
    (R : G.MixedBehavioralContinuationRealization fuel)
    (roots : G.observed.RootPresentation) :
    (R.continuationHom roots).DeclaredRootSurjective := by
  intro targetRoot htargetRoot
  exact ⟨targetRoot, htargetRoot, rfl⟩

/-- The continuation certificate gives rootwise exact semantic deviation
coverage. -/
theorem continuationHom_outcomeDeviationCompleteAt
    (R : G.MixedBehavioralContinuationRealization fuel)
    (roots : G.observed.RootPresentation)
    (profile : G.observed.MixedProfile) :
    (R.continuationHom roots).OutcomeDeviationCompleteAt
      profile := by
  intro current hroot i targetStrategy
  obtain ⟨sourceStrategy, hrealizes⟩ :=
    R.realize_deviation
      profile current i targetStrategy
  refine ⟨sourceStrategy, ?_⟩
  change
    G.behavioralStoppedPayoffLawFrom
        (Function.update
          (R.mapProfile profile)
          i targetStrategy)
        current fuel =
      G.mixedStoppedPayoffLawFrom
        (Function.update profile i sourceStrategy)
        current fuel
  exact hrealizes

/-- A continuation-wide realization preserves and reflects bounded Nash on presentation-designated continuations. -/
theorem isNashOnRootsAtFuel_iff
    [Preorder V]
    (R : G.MixedBehavioralContinuationRealization fuel)
    (roots : G.observed.RootPresentation)
    (utility :
      PMF (Option (N → U)) → N → V)
    (profile : G.observed.MixedProfile) :
    G.IsMixedNashOnRootsAtFuel
        roots utility profile fuel ↔
      G.IsBehavioralNashOnRootsAtFuel
        roots utility (R.mapProfile profile) fuel := by
  change
    (G.mixedContinuationFamilyOnRoots
      roots fuel).IsNashOnRoots
        (fun _ => utility) profile ↔
      (G.behavioralContinuationFamilyOnRoots
        roots fuel).IsNashOnRoots
          (fun _ => utility)
          ((R.continuationHom roots).mapProfile profile)
  apply
    (R.continuationHom roots).isNashOnRoots_iff_of_outcomeDeviationCompleteAt
      (profile := profile)
  · intro root outcome i
    rfl
  · exact
      R.continuationHom_declaredRootSurjective roots
  · exact
      R.continuationHom_outcomeDeviationCompleteAt roots profile

end MixedBehavioralContinuationRealization

end ExtensiveGame.ObservedChanceGame
