/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.Math.Probability.PMF.ConditionalSampling
import EconCSLib.Math.Probability.PMF.ConditionalProduct
import EconCSLib.GameTheory.ExtensiveGame.Observed.Kuhn

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Posterior

Batch and sequential posterior conditioning of complete pure plans.
-/

namespace ExtensiveGame.ObservedGame

variable {N U : Type*} (G : ObservedGame N U)

namespace PureStrategy

/-- A pure contingent plan agrees with one remembered personal decision. -/
def AgreesWithDecision {i : N}
    (strategy : G.PureStrategy i)
    (decision : G.PersonalDecision i) : Prop :=
  strategy decision.1 = decision.2

/-- A pure contingent plan agrees with every information/action record in a
remembered decision sequence. -/
def AgreesWithDecisions {i : N}
    (strategy : G.PureStrategy i)
    (decisions : List (G.PersonalDecision i)) : Prop :=
  ∀ decision ∈ decisions,
    strategy.AgreesWithDecision G decision

/-- The event of complete pure plans agreeing with a remembered decision
sequence. -/
def agreesWithDecisionsSet {i : N}
    (decisions : List (G.PersonalDecision i)) :
    Set (G.PureStrategy i) :=
  {strategy |
    strategy.AgreesWithDecisions G decisions}

@[simp]
theorem agreesWithDecisions_nil {i : N}
    (strategy : G.PureStrategy i) :
    strategy.AgreesWithDecisions G [] := by
  simp [AgreesWithDecisions]

@[simp]
theorem agreesWithDecisions_cons {i : N}
    (strategy : G.PureStrategy i)
    (decision : G.PersonalDecision i)
    (decisions : List (G.PersonalDecision i)) :
    strategy.AgreesWithDecisions
        G (decision :: decisions) ↔
      strategy.AgreesWithDecision G decision ∧
        strategy.AgreesWithDecisions G decisions := by
  simp [AgreesWithDecisions]

@[simp]
theorem agreesWithDecisions_append {i : N}
    (strategy : G.PureStrategy i)
    (first second :
      List (G.PersonalDecision i)) :
    strategy.AgreesWithDecisions
        G (first ++ second) ↔
      strategy.AgreesWithDecisions G first ∧
        strategy.AgreesWithDecisions G second := by
  constructor
  · intro hagrees
    constructor
    · intro decision hmem
      exact
        hagrees decision
          (List.mem_append_left second hmem)
    · intro decision hmem
      exact
        hagrees decision
          (List.mem_append_right first hmem)
  · rintro ⟨hfirst, hsecond⟩ decision hmem
    rcases List.mem_append.mp hmem with
      hmem | hmem
    · exact hfirst decision hmem
    · exact hsecond decision hmem

@[simp]
theorem mem_agreesWithDecisionsSet {i : N}
    (strategy : G.PureStrategy i)
    (decisions : List (G.PersonalDecision i)) :
    strategy ∈ agreesWithDecisionsSet G decisions ↔
      strategy.AgreesWithDecisions G decisions :=
  Iff.rfl

end PureStrategy

namespace MixedStrategy

/-- A remembered decision sequence has positive probability under a mixed
plan when some supported pure plan agrees with every recorded decision. -/
def DecisionsPossible {i : N}
    (strategy : G.MixedStrategy i)
    (decisions : List (G.PersonalDecision i)) : Prop :=
  ∃ pureStrategy ∈
      PureStrategy.agreesWithDecisionsSet G decisions,
    pureStrategy ∈ strategy.support

/-- Normalize a mixed plan on the positive event that it agrees with a
remembered decision sequence. -/
noncomputable def conditionOnDecisions {i : N}
    (strategy : G.MixedStrategy i)
    (decisions : List (G.PersonalDecision i))
    (hpossible :
      strategy.DecisionsPossible G decisions) :
    G.MixedStrategy i :=
  strategy.filter
    (PureStrategy.agreesWithDecisionsSet G decisions)
    hpossible

/-- The support of a conditioned mixed plan is exactly the supported pure
plans consistent with the conditioning sequence. -/
theorem mem_support_conditionOnDecisions_iff
    {i : N}
    (strategy : G.MixedStrategy i)
    (decisions : List (G.PersonalDecision i))
    (hpossible :
      strategy.DecisionsPossible G decisions)
    (pureStrategy : G.PureStrategy i) :
    pureStrategy ∈
        (strategy.conditionOnDecisions
          G decisions hpossible).support ↔
      pureStrategy.AgreesWithDecisions G decisions ∧
        pureStrategy ∈ strategy.support := by
  exact PMF.mem_support_filter_iff hpossible

/-- The empty decision sequence is possible under every mixed plan. -/
theorem decisionsPossible_nil {i : N}
    (strategy : G.MixedStrategy i) :
    strategy.DecisionsPossible G [] := by
  obtain ⟨pureStrategy, hsupported⟩ :=
    strategy.support_nonempty
  exact
    ⟨pureStrategy,
      by simp [PureStrategy.agreesWithDecisionsSet],
      hsupported⟩

/-- Conditioning on the empty decision sequence changes no mixed plan. -/
theorem conditionOnDecisions_nil {i : N}
    (strategy : G.MixedStrategy i)
    (hpossible :
      strategy.DecisionsPossible G []) :
    strategy.conditionOnDecisions
        G [] hpossible =
      strategy := by
  ext pureStrategy
  simp [conditionOnDecisions, PMF.filter_apply,
    PureStrategy.agreesWithDecisionsSet,
    strategy.tsum_coe]

/-- The action law of a mixed plan after conditioning on the recorded own
decisions.

On a zero-mass record sequence, the value is strategically irrelevant for
execution from the selected root.  The unconditional marginal is used as a
total, choice-free fallback. -/
noncomputable def conditionalActionLaw {i : N}
    (strategy : G.MixedStrategy i)
    (decisions : List (G.PersonalDecision i))
    (information : G.InfoState i) :
    PMF (G.InfoAction i information) := by
  classical
  exact
    if hpossible :
        strategy.DecisionsPossible G decisions then
      (strategy.conditionOnDecisions
        G decisions hpossible).map
          (fun pureStrategy =>
            pureStrategy information)
    else
      strategy.map
        (fun pureStrategy =>
          pureStrategy information)

/-- On a positive consistency event, the total conditional action law is the
declared conditional marginal. -/
theorem conditionalActionLaw_of_possible
    {i : N}
    (strategy : G.MixedStrategy i)
    (decisions : List (G.PersonalDecision i))
    (information : G.InfoState i)
    (hpossible :
      strategy.DecisionsPossible G decisions) :
    strategy.conditionalActionLaw
        G decisions information =
      (strategy.conditionOnDecisions
        G decisions hpossible).map
          (fun pureStrategy =>
            pureStrategy information) := by
  classical
  simp [conditionalActionLaw, hpossible]

/-- On a zero-mass consistency event, the total conditional action law uses
the unconditional action marginal. -/
theorem conditionalActionLaw_of_impossible
    {i : N}
    (strategy : G.MixedStrategy i)
    (decisions : List (G.PersonalDecision i))
    (information : G.InfoState i)
    (himpossible :
      ¬ strategy.DecisionsPossible G decisions) :
    strategy.conditionalActionLaw
        G decisions information =
      strategy.map
        (fun pureStrategy =>
          pureStrategy information) := by
  classical
  simp [conditionalActionLaw, himpossible]

/-- With no prior continuation-local decisions, conditional
behavioralization is exactly the ordinary mixed action marginal. -/
theorem conditionalActionLaw_nil
    {i : N}
    (strategy : G.MixedStrategy i)
    (information : G.InfoState i) :
    strategy.conditionalActionLaw
        G [] information =
      strategy.map
        (fun pureStrategy =>
          pureStrategy information) := by
  rw [strategy.conditionalActionLaw_of_possible
    G [] information
    (strategy.decisionsPossible_nil G)]
  rw [strategy.conditionOnDecisions_nil
    G (strategy.decisionsPossible_nil G)]

/-- Posterior mixed-plan law obtained by exposing a chronological sequence of
the player's own decisions one at a time.

Sequential conditioning is definitionally suited to execution induction: when
one more decision is observed, the current posterior is conditioned on one
additional evaluation fiber.  Zero-mass prefixes use the total fallback from
`PMF.conditionOnFiber` and therefore remain harmless off path. -/
noncomputable def posteriorAfterDecisions {i : N}
    (strategy : G.MixedStrategy i)
    (decisions : List (G.PersonalDecision i)) :
    G.MixedStrategy i :=
  decisions.foldl
    (fun posterior decision =>
      posterior.conditionOnFiber
        (fun pureStrategy =>
          pureStrategy decision.1)
        decision.2)
    strategy

@[simp]
theorem posteriorAfterDecisions_nil {i : N}
    (strategy : G.MixedStrategy i) :
    strategy.posteriorAfterDecisions G [] =
      strategy :=
  rfl

/-- Appending one remembered decision performs exactly one additional
posterior-fiber update. -/
theorem posteriorAfterDecisions_append_singleton
    {i : N}
    (strategy : G.MixedStrategy i)
    (decisions : List (G.PersonalDecision i))
    (decision : G.PersonalDecision i) :
    strategy.posteriorAfterDecisions
        G (decisions ++ [decision]) =
      (strategy.posteriorAfterDecisions
        G decisions).conditionOnFiber
          (fun pureStrategy =>
            pureStrategy decision.1)
          decision.2 := by
  simp [posteriorAfterDecisions, List.foldl_append]

/-- Current action marginal of the sequential posterior after a remembered
decision sequence. -/
noncomputable def sequentialConditionalActionLaw
    {i : N}
    (strategy : G.MixedStrategy i)
    (decisions : List (G.PersonalDecision i))
    (information : G.InfoState i) :
    PMF (G.InfoAction i information) :=
  (strategy.posteriorAfterDecisions
    G decisions).map
      (fun pureStrategy =>
        pureStrategy information)

@[simp]
theorem sequentialConditionalActionLaw_nil
    {i : N}
    (strategy : G.MixedStrategy i)
    (information : G.InfoState i) :
    strategy.sequentialConditionalActionLaw
        G [] information =
      strategy.map
        (fun pureStrategy =>
          pureStrategy information) :=
  rfl

end MixedStrategy

namespace BehavioralStrategy

/-- Coordinate-law family remaining after sequentially exposing a list of
personal decisions from an independently sampled behavioral table. -/
noncomputable def actionLawsAfterDecisions
    {i : N}
    (strategy : G.BehavioralStrategy i)
    (decisions : List (G.PersonalDecision i)) :
    G.BehavioralStrategy i := by
  classical
  exact
    decisions.foldl
      (fun laws decision =>
        Function.update laws decision.1
          ((laws decision.1).conditionOnFiber
            id decision.2))
      strategy

/-- Sequentially conditioning the complete independently sampled table is
again an independent table with the exposed coordinate laws updated one at a
time. -/
theorem toMixed_posteriorAfterDecisions
    {i : N}
    [Fintype (G.InfoState i)]
    (strategy : G.BehavioralStrategy i)
    (decisions : List (G.PersonalDecision i)) :
    (strategy.toMixed G).posteriorAfterDecisions
        G decisions =
      PMF.fintypePi
        (strategy.actionLawsAfterDecisions
          G decisions) := by
  classical
  induction decisions generalizing strategy with
  | nil =>
      rfl
  | cons decision decisions ih =>
      simp only [
        MixedStrategy.posteriorAfterDecisions,
        actionLawsAfterDecisions,
        List.foldl_cons]
      rw [show strategy.toMixed G =
        PMF.fintypePi strategy from rfl]
      let updatedStrategy :
          G.BehavioralStrategy i :=
        Function.update strategy decision.1
          ((strategy decision.1).conditionOnFiber
            id decision.2)
      have hcondition :
          (PMF.fintypePi strategy).conditionOnFiber
              (fun pureStrategy =>
                pureStrategy decision.1)
              decision.2 =
            PMF.fintypePi updatedStrategy := by
        exact
          PMF.fintypePi_conditionOnFiber_apply
            strategy decision.1 decision.2
      refine
        (congrArg
          (fun initial =>
            decisions.foldl
              (fun posterior later =>
                posterior.conditionOnFiber
                  (fun pureStrategy =>
                    pureStrategy later.1)
                  later.2)
              initial)
          hcondition).trans ?_
      simpa [updatedStrategy,
        MixedStrategy.posteriorAfterDecisions,
        actionLawsAfterDecisions] using
          (ih (strategy := updatedStrategy))

/-- Exposing decisions at other information states leaves the current
coordinate law unchanged. -/
theorem actionLawsAfterDecisions_apply_of_ne
    {i : N}
    (strategy : G.BehavioralStrategy i)
    (decisions : List (G.PersonalDecision i))
    (information : G.InfoState i)
    (hdistinct :
      ∀ decision ∈ decisions,
        decision.1 ≠ information) :
    strategy.actionLawsAfterDecisions
        G decisions information =
      strategy information := by
  classical
  induction decisions generalizing strategy with
  | nil =>
      rfl
  | cons decision decisions ih =>
      simp only [actionLawsAfterDecisions,
        List.foldl_cons]
      have htail :=
        ih
          (strategy :=
            Function.update strategy decision.1
              ((strategy decision.1).conditionOnFiber
                id decision.2))
          (by
            intro later hlater
            exact
              hdistinct later (by simp [hlater]))
      unfold actionLawsAfterDecisions at htail
      rw [htail]
      unfold Function.update
      split
      · rename_i heq
        exact
          ((hdistinct decision (by simp))
            heq.symm).elim
      · rfl

/-- The posterior independently sampled table retains the original action
marginal at every information state not listed among the exposed prior
decisions. -/
theorem toMixed_posteriorAfterDecisions_actionMarginal
    {i : N}
    [Fintype (G.InfoState i)]
    (strategy : G.BehavioralStrategy i)
    (decisions : List (G.PersonalDecision i))
    (information : G.InfoState i)
    (hdistinct :
      ∀ decision ∈ decisions,
        decision.1 ≠ information) :
    ((strategy.toMixed G).posteriorAfterDecisions
        G decisions).map
          (fun pureStrategy =>
            pureStrategy information) =
      strategy information := by
  classical
  rw [strategy.toMixed_posteriorAfterDecisions
    G decisions]
  calc
    (PMF.fintypePi
      (strategy.actionLawsAfterDecisions
        G decisions)).map
        (fun pureStrategy =>
          pureStrategy information) =
      strategy.actionLawsAfterDecisions
        G decisions information :=
      PMF.fintypePi_map_apply
        (strategy.actionLawsAfterDecisions
          G decisions)
        information
    _ = strategy information :=
      strategy.actionLawsAfterDecisions_apply_of_ne
        G decisions information hdistinct

end BehavioralStrategy

/-- One chronological personal-decision sequence for every player. -/
abbrev PersonalDecisionHistories :=
  (i : N) → List (G.PersonalDecision i)

/-- The own-decision sequences accumulated after a selected continuation
root, extracted from a later complete history. -/
def relativeOwnDecisionHistories
    [DecidableEq N]
    (root current :
      G.base.toArena.HistoryFrom G.base.init) :
    G.PersonalDecisionHistories :=
  fun i =>
    (G.ownDecisionHistory i current).drop
      (G.ownDecisionHistory i root).length

@[simp]
theorem relativeOwnDecisionHistories_self
    [DecidableEq N]
    (current :
      G.base.toArena.HistoryFrom G.base.init)
    (i : N) :
    G.relativeOwnDecisionHistories
        current current i =
      [] := by
  simp [relativeOwnDecisionHistories]

/-- A chance or another player's move leaves player `i`'s
continuation-relative own-decision sequence unchanged. -/
theorem relativeOwnDecisionHistories_snoc_of_not_mover
    [DecidableEq N]
    (root :
      G.base.toArena.HistoryFrom G.base.init)
    {state : G.base.State}
    (suffix :
      G.base.toArena.History root.1 state)
    (action : G.base.Action state)
    (i : N)
    (hmover :
      G.base.mover state ≠ some i) :
    G.relativeOwnDecisionHistories
        root
        ⟨G.base.next state action,
          root.2.append (suffix.snoc action)⟩
        i =
      G.relativeOwnDecisionHistories
        root
        ⟨state, root.2.append suffix⟩
        i := by
  unfold relativeOwnDecisionHistories
  rw [Arena.History.append_snoc]
  rw [G.ownDecisionHistory_snoc_of_not_mover
    i (root.2.append suffix) action hmover]

/-- A player's move appends exactly its current information/action record to
that player's continuation-relative sequence. -/
theorem relativeOwnDecisionHistories_snoc_of_mover
    [DecidableEq N]
    (root :
      G.base.toArena.HistoryFrom G.base.init)
    {state : G.base.State}
    (suffix :
      G.base.toArena.History root.1 state)
    (action : G.base.Action state)
    (i : N)
    (hmover :
      G.base.mover state = some i) :
    G.relativeOwnDecisionHistories
        root
        ⟨G.base.next state action,
          root.2.append (suffix.snoc action)⟩
        i =
      G.relativeOwnDecisionHistories
          root
          ⟨state, root.2.append suffix⟩
          i ++
        [G.personalDecisionAt
          i ⟨state, root.2.append suffix⟩
          hmover action] := by
  have hprefix :=
    G.ownDecisionHistory_prefix_append
      i root.2 suffix
  have hlength :
      (G.ownDecisionHistory i root).length ≤
        (G.ownDecisionHistory i
          ⟨state, root.2.append suffix⟩).length :=
    List.IsPrefix.length_le hprefix
  unfold relativeOwnDecisionHistories
  rw [Arena.History.append_snoc]
  rw [G.ownDecisionHistory_snoc_of_mover
    i (root.2.append suffix) action hmover]
  rw [List.drop_append_of_le_length hlength]

/-- No absent-mindedness also separates the current information state from
every decision in the continuation-relative suffix. -/
theorem HasNoAbsentMindedness.info_ne_of_mem_relativeOwnDecisionHistories
    [DecidableEq N]
    {i : N}
    (hnoAbsent : G.HasNoAbsentMindedness i)
    (root current :
      G.base.toArena.HistoryFrom G.base.init)
    (hmover :
      G.base.mover current.1 = some i)
    (decision : G.PersonalDecision i)
    (hmem :
      decision ∈
        G.relativeOwnDecisionHistories
          root current i) :
    decision.1 ≠
      G.infoAt current i hmover := by
  apply
    hnoAbsent.info_ne_of_mem_ownDecisionHistory
      current hmover decision
  exact
    (List.drop_sublist
      (G.ownDecisionHistory i root).length
      (G.ownDecisionHistory i current)).subset
        hmem


end ExtensiveGame.ObservedGame
