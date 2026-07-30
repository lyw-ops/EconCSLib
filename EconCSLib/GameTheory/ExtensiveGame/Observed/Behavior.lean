/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Chance

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.Behavior

Information-indexed behavioral strategies for history-indexed observed EFGs.

Unlike the older state-indexed finite-simplex API in `BehaviorStrategy.lean`,
this layer makes information-set consistency structural:

```lean
(information : G.InfoState i) → PMF (G.InfoAction i information)
```

No finiteness assumption is imposed on action types.  For an
`ObservedChanceGame`, a behavioral profile induces a terminal-aware stochastic
history policy: player histories use the acting player's information-indexed
law, while chance histories use the game's declared chance kernel exactly.

## Main definitions

* `ObservedGame.BehavioralStrategy` and `BehavioralProfile`.
* `ObservedGame.BehavioralProfile.actionLawAt`.
* `ObservedGame.BehavioralProfile.deviate`.
* `ObservedChanceGame.BehavioralProfile.toHistoryPolicy`.

## Main results

* `ObservedChanceGame.BehavioralProfile.toHistoryPolicy_of_mover`.
* `ObservedChanceGame.BehavioralProfile.toHistoryPolicy_of_chance`.
* `ObservedChanceGame.BehavioralProfile.toHistoryPolicy_chanceConsistent`.
-/

namespace ExtensiveGame.ObservedGame

variable {N U : Type*} (G : ObservedGame N U)

/-- A behavioral strategy for player `i`, indexed only by that player's
decision information state. -/
abbrev BehavioralStrategy (i : N) :=
  (information : G.InfoState i) →
    PMF (G.InfoAction i information)

/-- One information-indexed behavioral strategy for every player. -/
abbrev BehavioralProfile :=
  (i : N) → G.BehavioralStrategy i

/-- The concrete legal-action law induced by a behavioral strategy at a
history controlled by its player. -/
noncomputable def BehavioralStrategy.actionLawAt {i : N}
    (strategy : G.BehavioralStrategy i)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (hmover : G.base.mover history.1 = some i) :
    PMF (G.base.Action history.1) :=
  (strategy (G.infoAt history i hmover)).map
    (G.actionEquiv history i hmover)

/-- The concrete legal-action law induced by a behavioral profile at a
player-controlled history. -/
noncomputable def BehavioralProfile.actionLawAt
    (profile : G.BehavioralProfile)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (i : N) (hmover : G.base.mover history.1 = some i) :
    PMF (G.base.Action history.1) :=
  (profile i).actionLawAt G history hmover

/-- Equal information states force a behavioral profile to choose the same
packaged abstract action law. -/
theorem BehavioralProfile.actionLaw_eq_of_infoState_eq
    (profile : G.BehavioralProfile) (i : N)
    (history₁ history₂ :
      G.base.toArena.HistoryFrom G.base.init)
    (hmover₁ : G.base.mover history₁.1 = some i)
    (hmover₂ : G.base.mover history₂.1 = some i)
    (hsame :
      G.infoAt history₁ i hmover₁ =
        G.infoAt history₂ i hmover₂) :
    (⟨G.infoAt history₁ i hmover₁,
        profile i (G.infoAt history₁ i hmover₁)⟩ :
      Σ information : G.InfoState i,
        PMF (G.InfoAction i information)) =
      ⟨G.infoAt history₂ i hmover₂,
        profile i (G.infoAt history₂ i hmover₂)⟩ :=
  congrArg
    (fun information : G.InfoState i =>
      (⟨information, profile i information⟩ :
        Σ state : G.InfoState i, PMF (G.InfoAction i state)))
    hsame

/-- Unilateral deviation of an information-indexed behavioral profile. -/
def BehavioralProfile.deviate [DecidableEq N]
    (profile : G.BehavioralProfile) (who : N)
    (deviation : G.BehavioralStrategy who) :
    G.BehavioralProfile :=
  Function.update profile who deviation

@[simp]
theorem BehavioralProfile.deviate_same [DecidableEq N]
    (profile : G.BehavioralProfile) (who : N)
    (deviation : G.BehavioralStrategy who) :
    profile.deviate G who deviation who = deviation := by
  simp [BehavioralProfile.deviate]

@[simp]
theorem BehavioralProfile.deviate_of_ne [DecidableEq N]
    (profile : G.BehavioralProfile) (who : N)
    (deviation : G.BehavioralStrategy who)
    {other : N} (hne : other ≠ who) :
    profile.deviate G who deviation other = profile other := by
  simp [BehavioralProfile.deviate, hne]

end ExtensiveGame.ObservedGame

namespace ExtensiveGame.ObservedChanceGame

variable {N U : Type*} (G : ObservedChanceGame N U)

namespace BehavioralProfile

/-- The stochastic history policy induced by an observed-EFG behavioral
profile and the declared chance kernels. -/
noncomputable def toHistoryPolicy
    (profile : G.observed.BehavioralProfile) :
    G.observed.base.toArena.StochasticHistoryPolicy
      G.observed.base.init :=
  fun history hnonterminal =>
    match hmover : G.observed.base.mover history.1 with
    | some i =>
        profile.actionLawAt G.observed history i hmover
    | none =>
        G.chanceKernel history ⟨hmover, hnonterminal⟩

/-- At a player history, the induced policy is exactly that player's
information-indexed concrete action law. -/
theorem toHistoryPolicy_of_mover
    (profile : G.observed.BehavioralProfile)
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hnonterminal :
      ¬ G.observed.base.isTerminal history.1)
    (i : N)
    (hmover : G.observed.base.mover history.1 = some i) :
    toHistoryPolicy G profile history hnonterminal =
      profile.actionLawAt G.observed history i hmover := by
  rw [toHistoryPolicy]
  split
  · rename_i j hj
    have hji : j = i := by
      exact Option.some.inj (hj.symm.trans hmover)
    subst j
    rfl
  · rename_i hnone
    rw [hmover] at hnone
    contradiction

/-- At a chance history, the induced policy is exactly the declared chance
kernel. -/
theorem toHistoryPolicy_of_chance
    (profile : G.observed.BehavioralProfile)
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hnonterminal :
      ¬ G.observed.base.isTerminal history.1)
    (hmover : G.observed.base.mover history.1 = none) :
    toHistoryPolicy G profile history hnonterminal =
      G.chanceKernel history ⟨hmover, hnonterminal⟩ := by
  rw [toHistoryPolicy]
  split
  · rename_i i hi
    rw [hmover] at hi
    contradiction
  · rfl

/-- Every behavioral-profile history policy is chance-consistent. -/
theorem toHistoryPolicy_chanceConsistent
    (profile : G.observed.BehavioralProfile) :
    G.ChanceConsistent (toHistoryPolicy G profile) := by
  intro history hnonterminal hmover
  exact
    toHistoryPolicy_of_chance G profile history hnonterminal hmover

end BehavioralProfile

end ExtensiveGame.ObservedChanceGame
