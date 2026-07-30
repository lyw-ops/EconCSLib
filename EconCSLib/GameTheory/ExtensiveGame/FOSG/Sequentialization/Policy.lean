/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.Core

/-!
# EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.Policy

Policies and exact behavioral micro execution for one serialized macro step.
-/

namespace ExtensiveGame.FOSG.Sequentialization

universe uU

variable {n : ℕ} {U : Type uU}
  (G : FOSG (Fin (n + 1)) U)

/-! ### Policies for one serialized macro step -/

/-- Classical decidability of serializer terminality.

The compiler's semantic constructions are already noncomputable because
`PMF.map` is noncomputable; using proposition decidability here avoids adding
irrelevant decidability fields to `FOSG`. -/
noncomputable instance instDecidableIsTerminal
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U) :
    (state : (game G rootPayoff).State) →
      Decidable ((game G rootPayoff).isTerminal state) :=
  fun _ => Classical.propDecidable _

/-- Every serialized player-collection state is nonterminal in the presence
of a behavioral profile: its declared concrete action PMF has nonempty
support. -/
theorem behavioralPlayerState_not_terminal
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (profile : D.BehavioralProfile)
    (source : G.HistoryState)
    (hsource : ¬ G.isTerminal source.1)
    (count : ℕ) (hcount : count < n + 1)
    (collected : PartialAction G source.1 count) :
    ¬ (game G rootPayoff).isTerminal
      (.player source hsource count hcount collected) := by
  intro hterminal
  obtain ⟨action, _⟩ :=
    (behavioralActionLaws G D profile source hsource
      ⟨count, hcount⟩).support_nonempty
  exact hterminal.false action

/-- A deterministic policy used to describe the player-collection prefix for
one fixed FOSG joint action.

At player phases carrying `source`, it selects the corresponding component of
`jointAction`.  Its choices elsewhere are irrelevant and filled
noncomputably. -/
noncomputable def macroDeterministicPolicy
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U)
    (source : G.HistoryState)
    (jointAction : G.JointAction source.1) :
    (game G rootPayoff).toArena.HistoryPolicy
      (game G rootPayoff).init :=
  fun history hnonterminal => by
    cases hstate : history.1 with
    | root =>
        rw [hstate] at hnonterminal
        exact Classical.choice (not_isEmpty_iff.mp hnonterminal)
    | terminal macroHistory hterminal =>
        exfalso
        apply hnonterminal
        rw [hstate]
        exact ⟨fun action => nomatch action⟩
    | player macroHistory hmacroNonterminal count hcount collected =>
        by_cases hsource : macroHistory = source
        · subst macroHistory
          exact jointAction ⟨count, hcount⟩
        · rw [hstate] at hnonterminal
          exact Classical.choice (not_isEmpty_iff.mp hnonterminal)
    | chance macroHistory hmacroNonterminal action =>
        rw [hstate] at hnonterminal
        exact Classical.choice (not_isEmpty_iff.mp hnonterminal)

/-- Stochastic policy implementing one fixed FOSG joint action.

Player phases are Dirac choices.  Root and chance phases use the original FOSG
initial and transition kernels exactly. -/
noncomputable def macroPolicy
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U)
    (source : G.HistoryState)
    (jointAction : G.JointAction source.1) :
    (game G rootPayoff).toArena.StochasticHistoryPolicy
      (game G rootPayoff).init :=
  fun history hnonterminal => by
    cases hstate : history.1 with
    | root =>
        exact G.init
    | terminal macroHistory hterminal =>
        exfalso
        apply hnonterminal
        rw [hstate]
        exact ⟨fun action => nomatch action⟩
    | player macroHistory hmacroNonterminal count hcount collected =>
        by_cases hsource : macroHistory = source
        · subst macroHistory
          exact PMF.pure (jointAction ⟨count, hcount⟩)
        · rw [hstate] at hnonterminal
          exact PMF.pure
            (Classical.choice (not_isEmpty_iff.mp hnonterminal))
    | chance macroHistory hmacroNonterminal action =>
        exact G.transition macroHistory.1 action

/-- At every serialized player phase, the macro stochastic policy is the Dirac
law of its deterministic companion. -/
theorem macroPolicy_eq_pure_at_player
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U)
    (source : G.HistoryState)
    (jointAction : G.JointAction source.1)
    (macroHistory : G.HistoryState)
    (hmacroNonterminal : ¬ G.isTerminal macroHistory.1)
    (count : ℕ) (hcount : count < n + 1)
    (collected : PartialAction G macroHistory.1 count)
    (history :
      (game G rootPayoff).toArena.History
        (game G rootPayoff).init
        (.player macroHistory hmacroNonterminal count hcount collected))
    (hnonterminal :
      ¬ (game G rootPayoff).isTerminal
        (.player macroHistory hmacroNonterminal count hcount collected)) :
    macroPolicy G rootPayoff source jointAction
        ⟨.player macroHistory hmacroNonterminal count hcount collected,
          history⟩
        hnonterminal =
      PMF.pure
        (macroDeterministicPolicy G rootPayoff source jointAction
          ⟨.player macroHistory hmacroNonterminal count hcount collected,
            history⟩
          hnonterminal) := by
  by_cases hsource : macroHistory = source
  · subst macroHistory
    simp [macroPolicy, macroDeterministicPolicy]
  · simp [macroPolicy, macroDeterministicPolicy, hsource]

/-- On a canonical player state for `source`, the deterministic macro policy
selects the current component of `jointAction`. -/
theorem macroDeterministicPolicy_playerState
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U)
    (source : G.HistoryState)
    (hnonterminal : ¬ G.isTerminal source.1)
    (jointAction : G.JointAction source.1)
    (count : ℕ) (hcount : count < n + 1)
    (history :
      (game G rootPayoff).toArena.History
        (game G rootPayoff).init
        (playerState G source hnonterminal jointAction count hcount))
    (hstateNonterminal :
      ¬ (game G rootPayoff).isTerminal
        (playerState G source hnonterminal jointAction count hcount)) :
    macroDeterministicPolicy G rootPayoff source jointAction
        ⟨playerState G source hnonterminal jointAction count hcount,
          history⟩
        hstateNonterminal =
      jointAction ⟨count, hcount⟩ := by
  simp [macroDeterministicPolicy, playerState]

/-- A canonical player state is nonterminal because the fixed joint action
contains an action for its current player. -/
theorem playerState_not_terminal
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U)
    (source : G.HistoryState)
    (hnonterminal : ¬ G.isTerminal source.1)
    (jointAction : G.JointAction source.1)
    (count : ℕ) (hcount : count < n + 1) :
    ¬ (game G rootPayoff).isTerminal
      (playerState G source hnonterminal jointAction count hcount) := by
  intro hterminal
  exact hterminal.false (jointAction ⟨count, hcount⟩)

/-- The stochastic macro policy is Dirac throughout all remaining individual
player decisions. -/
theorem macroPolicy_isPureFor_playerPrefix
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U)
    (source : G.HistoryState)
    (hnonterminal : ¬ G.isTerminal source.1)
    (jointAction : G.JointAction source.1)
    (count : ℕ) (hcount : count < n + 1)
    (history :
      (game G rootPayoff).toArena.History
        (game G rootPayoff).init
        (playerState G source hnonterminal jointAction count hcount)) :
    (macroPolicy G rootPayoff source jointAction).IsPureFor
      (macroDeterministicPolicy G rootPayoff source jointAction)
      ⟨playerState G source hnonterminal jointAction count hcount,
        history⟩
      (n + 1 - count) := by
  induction hremaining : n + 1 - count using Nat.strong_induction_on
      generalizing count history with
  | h remaining ih =>
      have hpositive : 0 < remaining := by omega
      have hstateNonterminal :=
        playerState_not_terminal G rootPayoff source hnonterminal
          jointAction count hcount
      by_cases hnext : count + 1 < n + 1
      · have hremainingStep :
            remaining = (n + 1 - (count + 1)) + 1 := by
          omega
        rw [hremainingStep]
        simp only [Arena.StochasticHistoryPolicy.IsPureFor]
        simp only [dif_neg hstateNonterminal]
        constructor
        · exact
            macroPolicy_eq_pure_at_player G rootPayoff source
              jointAction source hnonterminal count hcount
              (PartialAction.ofJoint G jointAction count)
              history hstateNonterminal
        · rw [macroDeterministicPolicy_playerState G rootPayoff
            source hnonterminal jointAction count hcount history
            hstateNonterminal]
          have hnextState :=
            next_playerState_of_lt G source hnonterminal jointAction
              count hcount hnext
          change
            (macroPolicy G rootPayoff source jointAction).IsPureFor
              (macroDeterministicPolicy G rootPayoff source jointAction)
              ⟨next G
                  (playerState G source hnonterminal jointAction count
                    hcount)
                  (jointAction ⟨count, hcount⟩),
                history.snoc (jointAction ⟨count, hcount⟩)⟩
              (n + 1 - (count + 1))
          let nextHistory :
              (game G rootPayoff).toArena.History
                (game G rootPayoff).init
                (playerState G source hnonterminal jointAction
                  (count + 1) hnext) :=
            hnextState ▸
              history.snoc (jointAction ⟨count, hcount⟩)
          have hcurrent :
              (⟨next G
                    (playerState G source hnonterminal jointAction count
                      hcount)
                    (jointAction ⟨count, hcount⟩),
                  history.snoc (jointAction ⟨count, hcount⟩)⟩ :
                (game G rootPayoff).toArena.HistoryFrom
                  (game G rootPayoff).init) =
                ⟨playerState G source hnonterminal jointAction
                    (count + 1) hnext,
                  nextHistory⟩ := by
            apply Sigma.ext hnextState
            exact
              (eqRec_heq hnextState
                (history.snoc (jointAction ⟨count, hcount⟩))).symm
          rw [hcurrent]
          apply ih (n + 1 - (count + 1))
          · omega
          · rfl
      · have hremainingOne : remaining = 1 := by
          omega
        rw [hremainingOne]
        simp only [Arena.StochasticHistoryPolicy.IsPureFor]
        simp only [dif_neg hstateNonterminal]
        constructor
        · exact
            macroPolicy_eq_pure_at_player G rootPayoff source
              jointAction source hnonterminal count hcount
              (PartialAction.ofJoint G jointAction count)
              history hstateNonterminal
        · trivial

/-- Deterministic collection of all remaining player components ends at the
canonical transition-chance state. -/
theorem stoppedHistoryFrom_playerPrefix_fst
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U)
    (source : G.HistoryState)
    (hnonterminal : ¬ G.isTerminal source.1)
    (jointAction : G.JointAction source.1)
    (count : ℕ) (hcount : count < n + 1)
    (history :
      (game G rootPayoff).toArena.History
        (game G rootPayoff).init
        (playerState G source hnonterminal jointAction count hcount)) :
    ((game G rootPayoff).toArena.stoppedHistoryFrom
      (macroDeterministicPolicy G rootPayoff source jointAction)
      ⟨playerState G source hnonterminal jointAction count hcount,
        history⟩
      (n + 1 - count)).1 =
        chanceState G source hnonterminal jointAction := by
  induction hremaining : n + 1 - count using Nat.strong_induction_on
      generalizing count history with
  | h remaining ih =>
      have hpositive : 0 < remaining := by omega
      have hstateNonterminal :=
        playerState_not_terminal G rootPayoff source hnonterminal
          jointAction count hcount
      by_cases hnext : count + 1 < n + 1
      · have hremainingStep :
            remaining = (n + 1 - (count + 1)) + 1 := by
          omega
        rw [hremainingStep]
        rw [Arena.stoppedHistoryFrom_succ_of_not_terminal
          (macroDeterministicPolicy G rootPayoff source jointAction)
          ⟨playerState G source hnonterminal jointAction count hcount,
            history⟩
          (n + 1 - (count + 1)) hstateNonterminal]
        rw [macroDeterministicPolicy_playerState G rootPayoff
          source hnonterminal jointAction count hcount history
          hstateNonterminal]
        let nextHistoryRaw :=
          history.snoc (jointAction ⟨count, hcount⟩)
        have hnextState :=
          next_playerState_of_lt G source hnonterminal jointAction
            count hcount hnext
        let nextHistory :
            (game G rootPayoff).toArena.History
              (game G rootPayoff).init
              (playerState G source hnonterminal jointAction
                (count + 1) hnext) :=
          hnextState ▸ nextHistoryRaw
        have hcurrent :
            (⟨next G
                  (playerState G source hnonterminal jointAction count
                    hcount)
                  (jointAction ⟨count, hcount⟩),
                nextHistoryRaw⟩ :
              (game G rootPayoff).toArena.HistoryFrom
                (game G rootPayoff).init) =
              ⟨playerState G source hnonterminal jointAction
                  (count + 1) hnext,
                nextHistory⟩ := by
          apply Sigma.ext hnextState
          exact (eqRec_heq hnextState nextHistoryRaw).symm
        change
          ((game G rootPayoff).toArena.stoppedHistoryFrom
            (macroDeterministicPolicy G rootPayoff source jointAction)
            ⟨next G
                (playerState G source hnonterminal jointAction count
                  hcount)
                (jointAction ⟨count, hcount⟩),
              nextHistoryRaw⟩
            (n + 1 - (count + 1))).1 =
              chanceState G source hnonterminal jointAction
        rw [hcurrent]
        apply ih (n + 1 - (count + 1))
        · omega
        · rfl
      · have hremainingOne : remaining = 1 := by omega
        rw [hremainingOne]
        rw [Arena.stoppedHistoryFrom_succ_of_not_terminal
          (macroDeterministicPolicy G rootPayoff source jointAction)
          ⟨playerState G source hnonterminal jointAction count hcount,
            history⟩
          0 hstateNonterminal]
        rw [macroDeterministicPolicy_playerState G rootPayoff
          source hnonterminal jointAction count hcount history
          hstateNonterminal]
        change
          next G
              (playerState G source hnonterminal jointAction count
                hcount)
              (jointAction ⟨count, hcount⟩) =
            chanceState G source hnonterminal jointAction
        exact next_playerState_of_not_lt G source hnonterminal
          jointAction count hcount hnext

/-- The chance state reached after the deterministic player prefix is
nonterminal because its transition `PMF` has nonempty support. -/
theorem chanceState_not_terminal
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U)
    (source : G.HistoryState)
    (hnonterminal : ¬ G.isTerminal source.1)
    (jointAction : G.JointAction source.1) :
    ¬ (game G rootPayoff).isTerminal
      (chanceState G source hnonterminal jointAction) := by
  intro hterminal
  obtain ⟨nextWorld, _⟩ :=
    (G.transition source.1 jointAction).support_nonempty
  exact hterminal.false nextWorld

/-! ### Behavioral micro execution realizes the macro controller -/

/-- One fixed-action macro execution from a serialized player state peels off
its first Dirac player choice. -/
theorem macroExecutionFrom_player_eq_after
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U)
    (source : G.HistoryState)
    (hsource : ¬ G.isTerminal source.1)
    (count : ℕ) (hcount : count < n + 1)
    (collected : PartialAction G source.1 count)
    (history :
      (game G rootPayoff).toArena.History
        (game G rootPayoff).init
        (.player source hsource count hcount collected))
    (jointAction : G.JointAction source.1)
    (action : G.PlayerAction ⟨count, hcount⟩ source.1)
    (hcoordinate : jointAction ⟨count, hcount⟩ = action)
    (fuel : ℕ) :
    (game G rootPayoff).toArena.stochasticHistoryPMFFrom
        (macroPolicy G rootPayoff source jointAction)
        ⟨.player source hsource count hcount collected, history⟩
        (fuel + 1) =
      (game G rootPayoff).toArena.stochasticHistoryPMFFrom
        (macroPolicy G rootPayoff source jointAction)
        ⟨next G (.player source hsource count hcount collected) action,
          history.snoc action⟩ fuel := by
  have hnonterminal :
      ¬ (game G rootPayoff).isTerminal
        (.player source hsource count hcount collected) := by
    intro hterminal
    exact hterminal.false action
  rw [Arena.stochasticHistoryPMFFrom_succ_of_not_terminal
    (macroPolicy G rootPayoff source jointAction)
    ⟨.player source hsource count hcount collected, history⟩
    fuel hnonterminal]
  have hpolicy :
      macroPolicy G rootPayoff source jointAction
          ⟨.player source hsource count hcount collected, history⟩
          hnonterminal =
        PMF.pure (jointAction ⟨count, hcount⟩) := by
    simp [macroPolicy]
    rfl
  rw [hpolicy, hcoordinate]
  exact PMF.pure_bind action _

/-- At the transition-chance node, the genuine serialized behavioral policy
and the fixed-action macro policy have the same one-step execution law. -/
theorem behavioralChanceOneStep_eq_macro
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (profile : D.BehavioralProfile)
    (source : G.HistoryState)
    (hsource : ¬ G.isTerminal source.1)
    (jointAction : G.JointAction source.1)
    (history :
      (game G rootPayoff).toArena.History
        (game G rootPayoff).init
        (.chance source hsource jointAction)) :
    (game G rootPayoff).toArena.stochasticHistoryPMFFrom
        (serializedBehavioralHistoryPolicy G D rootPayoff
          sourceDeclaredRoot profile)
        ⟨.chance source hsource jointAction, history⟩ 1 =
      (game G rootPayoff).toArena.stochasticHistoryPMFFrom
        (macroPolicy G rootPayoff source jointAction)
        ⟨.chance source hsource jointAction, history⟩ 1 := by
  have hnonterminal :=
    chanceState_not_terminal G rootPayoff source hsource jointAction
  rw [Arena.stochasticHistoryPMFFrom_succ_of_not_terminal
    (serializedBehavioralHistoryPolicy G D rootPayoff
      sourceDeclaredRoot profile)
    ⟨.chance source hsource jointAction, history⟩ 0 hnonterminal]
  rw [Arena.stochasticHistoryPMFFrom_succ_of_not_terminal
    (macroPolicy G rootPayoff source jointAction)
    ⟨.chance source hsource jointAction, history⟩ 0 hnonterminal]
  rw [serializedBehavioralHistoryPolicy_chance G D rootPayoff
    sourceDeclaredRoot profile source hsource jointAction history
    hnonterminal]
  change
    (G.transition source.1 jointAction).bind _ =
      (G.transition source.1 jointAction).bind _
  apply congrArg (PMF.bind (G.transition source.1 jointAction))
  funext nextWorld
  rfl

/-- Prefix-parametric deferred-decisions theorem for the finite-player
serializer.

Executing the genuine observed-EFG behavioral policy for every remaining
player choice and the final transition-chance step is exactly the same PMF as
first completing the collected prefix with `PMF.finPiFrom` and then executing
the corresponding fixed-joint-action macro policy. -/
theorem behavioralPlayerExecution_eq_finPiFrom_bind_macro
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (profile : D.BehavioralProfile)
    (source : G.HistoryState)
    (hsource : ¬ G.isTerminal source.1) :
    ∀ (remaining count : ℕ)
      (hcount : count < n + 1)
      (htotal : count + remaining = n + 1)
      (collected : PartialAction G source.1 count)
      (history :
        (game G rootPayoff).toArena.History
          (game G rootPayoff).init
          (.player source hsource count hcount collected)),
      (game G rootPayoff).toArena.stochasticHistoryPMFFrom
          (serializedBehavioralHistoryPolicy G D rootPayoff
            sourceDeclaredRoot profile)
          ⟨.player source hsource count hcount collected, history⟩
          (remaining + 1) =
        (PMF.finPiFrom
          (behavioralActionLaws G D profile source hsource)
          remaining count htotal collected).bind fun jointAction =>
            (game G rootPayoff).toArena.stochasticHistoryPMFFrom
              (macroPolicy G rootPayoff source jointAction)
              ⟨.player source hsource count hcount collected, history⟩
              (remaining + 1) := by
  intro remaining
  induction remaining with
  | zero =>
      intro count hcount htotal collected history
      omega
  | succ remaining ih =>
      intro count hcount htotal collected history
      have hnonterminal :=
        behavioralPlayerState_not_terminal G D rootPayoff profile
          source hsource count hcount collected
      rw [Arena.stochasticHistoryPMFFrom_succ_of_not_terminal
        (serializedBehavioralHistoryPolicy G D rootPayoff
          sourceDeclaredRoot profile)
        ⟨.player source hsource count hcount collected, history⟩
        (remaining + 1) hnonterminal]
      rw [serializedBehavioralHistoryPolicy_player G D rootPayoff
        sourceDeclaredRoot profile source hsource count hcount collected
        history hnonterminal]
      change
        (behavioralActionLaws G D profile source hsource
          ⟨count, hcount⟩).bind _ = _
      rw [PMF.finPiFrom, PMF.bind_bind]
      apply congrArg
        (PMF.bind
          (behavioralActionLaws G D profile source hsource
            ⟨count, hcount⟩))
      funext action
      cases remaining with
      | zero =>
          have hcountEq : count = n := by omega
          subst count
          rw [PMF.finPiFrom, PMF.pure_bind]
          let jointAction : G.JointAction source.1 :=
            PartialAction.complete G
              (PartialAction.snoc G collected hcount action)
          have hcoordinate :
              jointAction ⟨n, hcount⟩ = action := by
            simp [jointAction, PartialAction.complete,
              PMF.FinPrefix.complete, PartialAction.snoc,
              PMF.FinPrefix.snoc]
          have hlast : ¬ n + 1 < n + 1 := by omega
          have hnext :
              next G
                  (.player source hsource n hcount collected)
                  action =
                .chance source hsource jointAction := by
            simp only [next, hlast, ↓reduceDIte]
            rfl
          let chanceHistory :
              (game G rootPayoff).toArena.History
                (game G rootPayoff).init
                (.chance source hsource jointAction) :=
            hnext ▸ history.snoc action
          have hcurrent :
              (⟨next G
                    (.player source hsource n hcount collected)
                    action,
                  history.snoc action⟩ :
                (game G rootPayoff).toArena.HistoryFrom
                  (game G rootPayoff).init) =
                ⟨.chance source hsource jointAction,
                  chanceHistory⟩ := by
            apply Sigma.ext hnext
            exact (eqRec_heq hnext (history.snoc action)).symm
          calc
            (game G rootPayoff).toArena.stochasticHistoryPMFFrom
                (serializedBehavioralHistoryPolicy G D rootPayoff
                  sourceDeclaredRoot profile)
                ⟨(game G rootPayoff).next
                    (.player source hsource n hcount collected)
                    action,
                  history.snoc action⟩ 1 =
              (game G rootPayoff).toArena.stochasticHistoryPMFFrom
                (macroPolicy G rootPayoff source jointAction)
                ⟨next G
                    (.player source hsource n hcount collected)
                    action,
                  history.snoc action⟩ 1 := by
                change
                  (game G rootPayoff).toArena.stochasticHistoryPMFFrom
                      (serializedBehavioralHistoryPolicy G D rootPayoff
                        sourceDeclaredRoot profile)
                      ⟨next G
                          (.player source hsource n hcount collected)
                          action,
                        history.snoc action⟩ 1 =
                    _
                rw [hcurrent]
                exact
                  behavioralChanceOneStep_eq_macro G D rootPayoff
                    sourceDeclaredRoot profile source hsource jointAction
                    chanceHistory
            _ =
              (game G rootPayoff).toArena.stochasticHistoryPMFFrom
                (macroPolicy G rootPayoff source jointAction)
                ⟨.player source hsource n hcount collected,
                  history⟩ 2 :=
              (macroExecutionFrom_player_eq_after G rootPayoff source
                hsource n hcount collected history jointAction
                action hcoordinate 1).symm
      | succ remaining =>
          have hnextCount : count + 1 < n + 1 := by omega
          let extended : PartialAction G source.1 (count + 1) :=
            PartialAction.snoc G collected hcount action
          have hnextState :
              next G
                  (.player source hsource count hcount collected)
                  action =
                .player source hsource (count + 1) hnextCount
                  extended := by
            simp [next, hnextCount, extended]
          let nextHistory :
              (game G rootPayoff).toArena.History
                (game G rootPayoff).init
                (.player source hsource (count + 1) hnextCount
                  extended) :=
            hnextState ▸ history.snoc action
          have hcurrent :
              (⟨next G
                    (.player source hsource count hcount collected)
                    action,
                  history.snoc action⟩ :
                (game G rootPayoff).toArena.HistoryFrom
                  (game G rootPayoff).init) =
                ⟨.player source hsource (count + 1) hnextCount
                    extended,
                  nextHistory⟩ := by
            apply Sigma.ext hnextState
            exact (eqRec_heq hnextState (history.snoc action)).symm
          change
            (game G rootPayoff).toArena.stochasticHistoryPMFFrom
                (serializedBehavioralHistoryPolicy G D rootPayoff
                  sourceDeclaredRoot profile)
                ⟨next G
                    (.player source hsource count hcount collected)
                    action,
                  history.snoc action⟩
                (remaining + 2) = _
          rw [hcurrent]
          rw [ih (count + 1) hnextCount (by omega)
            extended nextHistory]
          apply PMF.bind_congr_support
          intro jointAction hjoint
          have hprefix :
              (⟨count, hcount⟩ : Fin (n + 1)).val <
                count + 1 :=
            Nat.lt_succ_self count
          have hcoordinate :
              jointAction ⟨count, hcount⟩ = action := by
            calc
              jointAction ⟨count, hcount⟩ =
                  extended ⟨count, hcount⟩ hprefix :=
                PMF.finPiFrom_apply_eq_of_mem_support_of_lt
                  (behavioralActionLaws G D profile source hsource)
                  (remaining + 1) (count + 1) (by omega)
                  extended jointAction hjoint ⟨count, hcount⟩
                  hprefix
              _ = action := by
                simp [extended, PartialAction.snoc,
                  PMF.FinPrefix.snoc]
          rw [← hcurrent]
          exact
            (macroExecutionFrom_player_eq_after G rootPayoff source
              hsource count hcount collected history jointAction action
              hcoordinate (remaining + 2)).symm


end ExtensiveGame.FOSG.Sequentialization
