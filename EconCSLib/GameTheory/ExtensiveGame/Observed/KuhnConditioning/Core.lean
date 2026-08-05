/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Posterior

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Core

Mixed-profile posterior products and perfect-recall conditioning identities.
-/

namespace ExtensiveGame.ObservedGame

variable {N U : Type*} (G : ObservedGame N U)

namespace MixedProfile

/-- Update every player's mixed plan to the sequential posterior induced by
the supplied own-decision sequence. -/
noncomputable def posteriorAfterDecisions
    (profile : G.MixedProfile)
    (decisions : G.PersonalDecisionHistories) :
    G.MixedProfile :=
  fun i =>
    (profile i).posteriorAfterDecisions
      G (decisions i)

@[simp]
theorem posteriorAfterDecisions_apply
    (profile : G.MixedProfile)
    (decisions : G.PersonalDecisionHistories)
    (i : N) :
    profile.posteriorAfterDecisions
        G decisions i =
      (profile i).posteriorAfterDecisions
        G (decisions i) :=
  rfl

/-- At the continuation root, all playerwise posteriors are the original
mixed plans. -/
@[simp]
theorem posteriorAfterDecisions_empty
    (profile : G.MixedProfile) :
    profile.posteriorAfterDecisions
        G (fun _ => []) =
      profile := by
  funext i
  rfl

/-- After a represented player action, the continuation-relative posterior
profile updates exactly the acting player's plan law on the observed abstract
action fiber. -/
theorem posteriorAfterDecisions_relative_snoc_of_mover
    [DecidableEq N]
    (profile : G.MixedProfile)
    (root :
      G.base.toArena.HistoryFrom G.base.init)
    {state : G.base.State}
    (suffix :
      G.base.toArena.History root.1 state)
    (i : N)
    (hmover :
      G.base.mover state = some i)
    (hnonterminal :
      ¬ G.base.isTerminal state)
    (abstractAction :
      G.InfoAction i
        (G.infoAt
          ⟨state, root.2.append suffix⟩
          i hmover hnonterminal)) :
    profile.posteriorAfterDecisions
        G
        (G.relativeOwnDecisionHistories
          root
          ⟨G.base.next state
              (G.actionEquiv
                ⟨state, root.2.append suffix⟩
                i hmover hnonterminal abstractAction),
            root.2.append
              (suffix.snoc
                (G.actionEquiv
                  ⟨state, root.2.append suffix⟩
                  i hmover hnonterminal abstractAction))⟩) =
      Function.update
        (profile.posteriorAfterDecisions
          G
          (G.relativeOwnDecisionHistories
            root
            ⟨state, root.2.append suffix⟩))
        i
        (((profile i).posteriorAfterDecisions
            G
            (G.relativeOwnDecisionHistories
              root
              ⟨state, root.2.append suffix⟩
              i)).conditionOnFiber
          (fun pureStrategy =>
            pureStrategy
              (G.infoAt
                ⟨state, root.2.append suffix⟩
                i hmover hnonterminal))
          abstractAction) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp only [Function.update]
    change
      (profile i).posteriorAfterDecisions
          G
          (G.relativeOwnDecisionHistories
            root
            ⟨G.base.next state
                (G.actionEquiv
                  ⟨state, root.2.append suffix⟩
                  i hmover hnonterminal abstractAction),
              root.2.append
                (suffix.snoc
                  (G.actionEquiv
                    ⟨state, root.2.append suffix⟩
                    i hmover hnonterminal abstractAction))⟩
            i) =
        ((profile i).posteriorAfterDecisions
          G
          (G.relativeOwnDecisionHistories
            root
            ⟨state, root.2.append suffix⟩
            i)).conditionOnFiber
              (fun pureStrategy =>
                pureStrategy
                  (G.infoAt
                    ⟨state, root.2.append suffix⟩
                    i hmover hnonterminal))
              abstractAction
    rw [G.relativeOwnDecisionHistories_snoc_of_mover
      root suffix
      (G.actionEquiv
        ⟨state, root.2.append suffix⟩
        i hmover hnonterminal abstractAction)
      i hmover]
    rw [MixedStrategy.posteriorAfterDecisions_append_singleton]
    rw [G.personalDecisionAt_actionEquiv
      i ⟨state, root.2.append suffix⟩
      hmover hnonterminal abstractAction]
  · simp only [Function.update, hji]
    change
      (profile j).posteriorAfterDecisions
          G
          (G.relativeOwnDecisionHistories
            root
            ⟨G.base.next state
                (G.actionEquiv
                  ⟨state, root.2.append suffix⟩
                  i hmover hnonterminal abstractAction),
              root.2.append
                (suffix.snoc
                  (G.actionEquiv
                    ⟨state, root.2.append suffix⟩
                    i hmover hnonterminal abstractAction))⟩
            j) =
        (profile j).posteriorAfterDecisions
          G
          (G.relativeOwnDecisionHistories
            root
            ⟨state, root.2.append suffix⟩
            j)
    apply congrArg
      ((profile j).posteriorAfterDecisions G)
    apply G.relativeOwnDecisionHistories_snoc_of_not_mover
    intro hwrong
    exact hji (Option.some.inj (hwrong.symm.trans hmover))

end MixedProfile

namespace RecallCertificate

variable [DecidableEq N]

/-- Personal decisions remembered at an information state after removing the
part that occurred before `current`.

For information states not reachable from `current`, `drop` still makes this a
total definition.  Those values do not affect execution from the selected
root. -/
def rememberedFrom
    (certificate : G.RecallCertificate)
    (current :
      G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (information : G.InfoState i) :
    List (G.PersonalDecision i) :=
  (certificate.remembered i information).drop
    (G.ownDecisionHistory i current).length

/-- At a player-controlled continuation root, no continuation-local decision
has yet occurred. -/
@[simp]
theorem rememberedFrom_infoAt_current
    (certificate : G.RecallCertificate)
    (current :
      G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hmover :
      G.base.mover current.1 = some i)
    (hnonterminal :
      ¬ G.base.isTerminal current.1) :
    certificate.rememberedFrom
        G current i
        (G.infoAt current i hmover hnonterminal) =
      [] := by
  simp [rememberedFrom,
    certificate.remembered_infoAt _ _ _ hnonterminal]

/-- At a represented decision reachable from `current`, the relative
remembered sequence is the suffix of the extracted own-decision history after
the root prefix. -/
theorem rememberedFrom_infoAt_append
    (certificate : G.RecallCertificate)
    (current :
      G.base.toArena.HistoryFrom G.base.init)
    {finish : G.base.State}
    (suffix :
      G.base.toArena.History current.1 finish)
    (i : N)
    (hmover :
      G.base.mover finish = some i)
    (hnonterminal :
      ¬ G.base.isTerminal finish) :
    certificate.rememberedFrom
        G current i
        (G.infoAt
          ⟨finish, current.2.append suffix⟩
          i hmover hnonterminal) =
      (G.ownDecisionHistory i
        ⟨finish, current.2.append suffix⟩).drop
          (G.ownDecisionHistory i current).length := by
  rw [rememberedFrom,
    certificate.remembered_infoAt _ _ _ hnonterminal]

/-- At a reachable continuation decision, the pre-root personal history
followed by the relative remembered suffix reconstructs the complete personal
history. -/
theorem ownDecisionHistory_append_rememberedFrom_infoAt
    (certificate : G.RecallCertificate)
    (current :
      G.base.toArena.HistoryFrom G.base.init)
    {finish : G.base.State}
    (suffix :
      G.base.toArena.History current.1 finish)
    (i : N)
    (hmover :
      G.base.mover finish = some i)
    (hnonterminal :
      ¬ G.base.isTerminal finish) :
    G.ownDecisionHistory i current ++
        certificate.rememberedFrom
          G current i
          (G.infoAt
            ⟨finish, current.2.append suffix⟩
            i hmover hnonterminal) =
      G.ownDecisionHistory i
        ⟨finish, current.2.append suffix⟩ := by
  rw [certificate.rememberedFrom_infoAt_append
    G current suffix i hmover hnonterminal]
  exact
    (List.prefix_append_drop
      (G.ownDecisionHistory_prefix_append
        i current.2 suffix)).symm

/-- Behavioralize one arbitrary mixed plan from a selected continuation root
by conditioning only on the player's own decisions made since that root. -/
noncomputable def behavioralizeMixedFrom
    (certificate : G.RecallCertificate)
    (current :
      G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (strategy : G.MixedStrategy i) :
    G.BehavioralStrategy i :=
  fun information =>
    strategy.sequentialConditionalActionLaw
      G
      (certificate.rememberedFrom
        G current i information)
      information

/-- At a player-controlled continuation root, root-scoped
behavioralization uses exactly the unconditional mixed action marginal. -/
theorem behavioralizeMixedFrom_at_root
    (certificate : G.RecallCertificate)
    (current :
      G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hmover :
      G.base.mover current.1 = some i)
    (hnonterminal :
      ¬ G.base.isTerminal current.1)
    (strategy : G.MixedStrategy i) :
    certificate.behavioralizeMixedFrom
        G current i strategy
        (G.infoAt current i hmover hnonterminal) =
      strategy.map
        (fun pureStrategy =>
          pureStrategy
            (G.infoAt current i hmover hnonterminal)) := by
  unfold behavioralizeMixedFrom
  rw [certificate.rememberedFrom_infoAt_current
    G current i hmover hnonterminal]
  rfl

/-- At a represented continuation decision, root-scoped behavioralization is
the mixed action law conditioned on exactly the own-decision suffix accumulated
since the selected root. -/
theorem behavioralizeMixedFrom_at_append
    (certificate : G.RecallCertificate)
    (current :
      G.base.toArena.HistoryFrom G.base.init)
    {finish : G.base.State}
    (suffix :
      G.base.toArena.History current.1 finish)
    (i : N)
    (hmover :
      G.base.mover finish = some i)
    (hnonterminal :
      ¬ G.base.isTerminal finish)
    (strategy : G.MixedStrategy i) :
    certificate.behavioralizeMixedFrom
        G current i strategy
        (G.infoAt
          ⟨finish, current.2.append suffix⟩
          i hmover hnonterminal) =
      strategy.sequentialConditionalActionLaw
        G
        ((G.ownDecisionHistory i
          ⟨finish, current.2.append suffix⟩).drop
            (G.ownDecisionHistory i current).length)
        (G.infoAt
          ⟨finish, current.2.append suffix⟩
          i hmover hnonterminal) := by
  unfold behavioralizeMixedFrom
  rw [certificate.rememberedFrom_infoAt_append
    G current suffix i hmover hnonterminal]

/-- The concrete root action law of root-scoped behavioralization is exactly
the concrete action marginal of the source mixed plan. -/
theorem behavioralizeMixedFrom_actionLawAt_root
    (certificate : G.RecallCertificate)
    (current :
      G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hmover :
      G.base.mover current.1 = some i)
    (hnonterminal :
      ¬ G.base.isTerminal current.1)
    (strategy : G.MixedStrategy i) :
    (certificate.behavioralizeMixedFrom
        G current i strategy).actionLawAt
          G current hmover hnonterminal =
      strategy.map
        (fun pureStrategy =>
          pureStrategy.actionAt
            G current hmover hnonterminal) := by
  unfold BehavioralStrategy.actionLawAt
  rw [certificate.behavioralizeMixedFrom_at_root
    G current i hmover hnonterminal strategy]
  simpa [PureStrategy.actionAt,
    Function.comp_def] using
      PMF.map_comp
        (fun pureStrategy =>
          pureStrategy
            (G.infoAt current i hmover hnonterminal))
        strategy
        (G.actionEquiv current i hmover hnonterminal)

/-- Behavioralize every component of a mixed profile from the same
continuation root. -/
noncomputable def behavioralizeMixedProfileFrom
    (certificate : G.RecallCertificate)
    (current :
      G.base.toArena.HistoryFrom G.base.init)
    (profile : G.MixedProfile) :
    G.BehavioralProfile :=
  fun i =>
    certificate.behavioralizeMixedFrom
      G current i (profile i)

@[simp]
theorem behavioralizeMixedProfileFrom_apply
    (certificate : G.RecallCertificate)
    (current :
      G.base.toArena.HistoryFrom G.base.init)
    (profile : G.MixedProfile)
    (i : N) :
    certificate.behavioralizeMixedProfileFrom
        G current profile i =
      certificate.behavioralizeMixedFrom
        G current i (profile i) :=
  rfl

end RecallCertificate

namespace FiniteKuhnHypotheses

variable [DecidableEq N]

/-- The canonical recall certificate selected from the perfect-recall field of
the finite Kuhn hypotheses. -/
noncomputable def recallCertificate
    (h : G.FiniteKuhnHypotheses) :
    G.RecallCertificate :=
  h.perfectRecall.toRecallCertificate

/-- Root-scoped conditional behavioralization selected canonically from the
finite Kuhn hypotheses. -/
noncomputable def mixedToBehavioralProfileAt
    (h : G.FiniteKuhnHypotheses)
    (current :
      G.base.toArena.HistoryFrom G.base.init)
    (profile : G.MixedProfile) :
    G.BehavioralProfile :=
  h.recallCertificate.behavioralizeMixedProfileFrom
    G current profile

/-- At every decision reachable from the selected continuation root,
root-scoped behavioralization of an independently sampled behavioral table
recovers the source behavioral action law exactly. -/
theorem behavioralize_behavioralToMixed_at_append
    (h : G.FiniteKuhnHypotheses)
    (root :
      G.base.toArena.HistoryFrom G.base.init)
    {finish : G.base.State}
    (suffix :
      G.base.toArena.History root.1 finish)
    (i : N)
    (hmover :
      G.base.mover finish = some i)
    (hnonterminal :
      ¬ G.base.isTerminal finish)
    (strategy : G.BehavioralStrategy i) :
    h.recallCertificate.behavioralizeMixedFrom
        G root i
        (h.behavioralToMixedStrategy
          i strategy)
        (G.infoAt
          ⟨finish, root.2.append suffix⟩
          i hmover hnonterminal) =
      strategy
        (G.infoAt
          ⟨finish, root.2.append suffix⟩
          i hmover hnonterminal) := by
  classical
  letI : Finite (G.InfoState i) :=
    h.finiteInfoState i
  letI : Fintype (G.InfoState i) :=
    Fintype.ofFinite (G.InfoState i)
  rw [h.recallCertificate.behavioralizeMixedFrom_at_append
    G root suffix i hmover hnonterminal
    (h.behavioralToMixedStrategy i strategy)]
  unfold MixedStrategy.sequentialConditionalActionLaw
  change
    ((strategy.toMixed G).posteriorAfterDecisions
      G
      (G.relativeOwnDecisionHistories
        root
        ⟨finish, root.2.append suffix⟩
        i)).map
          (fun pureStrategy =>
            pureStrategy
              (G.infoAt
                ⟨finish, root.2.append suffix⟩
                i hmover hnonterminal)) =
      strategy
        (G.infoAt
          ⟨finish, root.2.append suffix⟩
          i hmover hnonterminal)
  apply
    strategy.toMixed_posteriorAfterDecisions_actionMarginal
      G
      (G.relativeOwnDecisionHistories
        root
        ⟨finish, root.2.append suffix⟩
        i)
      (G.infoAt
        ⟨finish, root.2.append suffix⟩
        i hmover hnonterminal)
  intro decision hmem
  exact
    HasNoAbsentMindedness.info_ne_of_mem_relativeOwnDecisionHistories
      (G := G) (h.noAbsentMindedness i) root
      ⟨finish, root.2.append suffix⟩
      hmover hnonterminal decision hmem

end FiniteKuhnHypotheses

end ExtensiveGame.ObservedGame
