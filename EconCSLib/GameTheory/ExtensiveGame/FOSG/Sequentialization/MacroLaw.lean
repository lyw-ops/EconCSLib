/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.Policy

/-!
# EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.MacroLaw

One-step macro-boundary laws and the exact kernel simulation.
-/

namespace ExtensiveGame.FOSG.Sequentialization

universe uU

variable {n : ℕ} {U : Type uU}
  (G : FOSG (Fin (n + 1)) U)

/-! ### Exact one-macro-step execution law -/

/-- Relation between an augmented FOSG macro state and a serialized EFG
complete history at its corresponding macro boundary. -/
def Rel
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (source : G.HistoryState)
    (target :
      (arena G).HistoryFrom (State.root : State G)) : Prop :=
  target.1 = boundary G source

/-- A serialized macro-boundary history is related to at most one augmented
FOSG history state. -/
theorem Rel.left_unique
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    {source₁ source₂ : G.HistoryState}
    {target :
      (arena G).HistoryFrom (State.root : State G)}
    (h₁ : Rel G source₁ target)
    (h₂ : Rel G source₂ target) :
    source₁ = source₂ :=
  boundary_injective G (h₁.symm.trans h₂)

/-- At a related nonterminal macro boundary, the genuine serialized
observed-EFG behavioral policy has exactly the mixture of canonical macro
execution laws induced by the source behavioral joint-action PMF.

This is the missing micro/macro realization equation: no quotient of
probabilities and no support-only approximation is used. -/
theorem serializedBehavioralExecution_eq_jointActionLaw_bind_macro
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (profile : D.BehavioralProfile)
    (source : G.HistoryState)
    (hsource : ¬ G.isTerminal source.1)
    (target :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init)
    (hrelated : Rel G source target) :
    (game G rootPayoff).toArena.stochasticHistoryPMFFrom
        (serializedBehavioralHistoryPolicy G D rootPayoff
          sourceDeclaredRoot profile)
        target (n + 2) =
      (D.jointActionLaw profile source hsource).bind
        (fun jointAction =>
          (game G rootPayoff).toArena.stochasticHistoryPMFFrom
            (macroPolicy G rootPayoff source jointAction)
            target (n + 2)) := by
  have htargetState :
      target.1 =
        .player source hsource 0 (Nat.zero_lt_succ n)
          (PartialAction.empty G source.1) := by
    exact
      hrelated.trans
        (boundary_of_not_terminal G source hsource)
  let startHistory :
      (game G rootPayoff).toArena.History
        (game G rootPayoff).init
        (.player source hsource 0 (Nat.zero_lt_succ n)
          (PartialAction.empty G source.1)) :=
    htargetState ▸ target.2
  let start :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init :=
    ⟨.player source hsource 0 (Nat.zero_lt_succ n)
        (PartialAction.empty G source.1),
      startHistory⟩
  have htargetEq : target = start := by
    apply Sigma.ext htargetState
    exact (eqRec_heq htargetState target.2).symm
  rw [htargetEq]
  exact
    behavioralPlayerExecution_eq_finPiFrom_bind_macro G D rootPayoff
      sourceDeclaredRoot profile source hsource
      (n + 1) 0 (Nat.zero_lt_succ n) (by omega)
      (PartialAction.empty G source.1) startHistory

/-- Exact target endpoint law for one serialized FOSG macro action.

The theorem returns the concrete target endpoint map because it depends on the
incoming target history.  The target stochastic execution is exactly the
source transition kernel pushed through this map, and every resulting endpoint
is the macro boundary corresponding to the appended FOSG history. -/
theorem exists_macroExecutionLaw
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U)
    (source : G.HistoryState)
    (jointAction : G.JointAction source.1)
    (target :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init)
    (hrelated : Rel G source target) :
    ∃ targetEndpoint :
        G.WorldState →
          (game G rootPayoff).toArena.HistoryFrom
            (game G rootPayoff).init,
      (game G rootPayoff).toArena.stochasticHistoryPMFFrom
          (macroPolicy G rootPayoff source jointAction)
          target (n + 2) =
        (G.transition source.1 jointAction).map targetEndpoint ∧
      ∀ nextWorld,
        (targetEndpoint nextWorld).1 =
          boundary G
            ⟨nextWorld,
              FOSG.History.snoc source.2 jointAction nextWorld⟩ := by
  have hnonterminal : ¬ G.isTerminal source.1 := by
    intro hterminal
    exact ((G.terminal_iff source.1).mp hterminal).false jointAction
  have hboundary :
      boundary G source =
        playerState G source hnonterminal jointAction 0
          (Nat.zero_lt_succ n) :=
    boundary_eq_playerState G source hnonterminal jointAction
  have htargetState :
      target.1 =
        playerState G source hnonterminal jointAction 0
          (Nat.zero_lt_succ n) :=
    hrelated.trans hboundary
  let startHistory :
      (game G rootPayoff).toArena.History
        (game G rootPayoff).init
        (playerState G source hnonterminal jointAction 0
          (Nat.zero_lt_succ n)) :=
    htargetState ▸ target.2
  let start :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init :=
    ⟨playerState G source hnonterminal jointAction 0
        (Nat.zero_lt_succ n),
      startHistory⟩
  have htargetEq : target = start := by
    apply Sigma.ext htargetState
    exact (eqRec_heq htargetState target.2).symm
  let deterministic :=
    macroDeterministicPolicy G rootPayoff source jointAction
  let stochastic :=
    macroPolicy G rootPayoff source jointAction
  let chanceHistory :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init :=
    (game G rootPayoff).toArena.stoppedHistoryFrom
      deterministic start (n + 1)
  have hchanceState :
      chanceHistory.1 =
        chanceState G source hnonterminal jointAction := by
    exact stoppedHistoryFrom_playerPrefix_fst G rootPayoff source
      hnonterminal jointAction 0 (Nat.zero_lt_succ n) startHistory
  let chancePath :
      (game G rootPayoff).toArena.History
        (game G rootPayoff).init
        (chanceState G source hnonterminal jointAction) :=
    hchanceState ▸ chanceHistory.2
  have hchanceHistoryEq :
      chanceHistory =
        (⟨chanceState G source hnonterminal jointAction,
            chancePath⟩ :
          (game G rootPayoff).toArena.HistoryFrom
            (game G rootPayoff).init) := by
    apply Sigma.ext hchanceState
    exact (eqRec_heq hchanceState chanceHistory.2).symm
  let targetEndpoint :
      G.WorldState →
        (game G rootPayoff).toArena.HistoryFrom
          (game G rootPayoff).init :=
    fun nextWorld =>
      ⟨boundary G
          ⟨nextWorld,
            FOSG.History.snoc source.2 jointAction nextWorld⟩,
        chancePath.snoc nextWorld⟩
  refine ⟨targetEndpoint, ?_, ?_⟩
  · rw [htargetEq]
    have hpure :=
      macroPolicy_isPureFor_playerPrefix G rootPayoff source
        hnonterminal jointAction 0 (Nat.zero_lt_succ n) startHistory
    have hprefix :
        (game G rootPayoff).toArena.stochasticHistoryPMFFrom
            stochastic start (n + 1) =
          PMF.pure chanceHistory := by
      exact
        Arena.stochasticHistoryPMFFrom_eq_pure_stoppedHistoryFrom
          stochastic deterministic start (n + 1) hpure
    have hadd :
        n + 2 = (n + 1) + 1 := by omega
    rw [hadd]
    rw [Arena.stochasticHistoryPMFFrom_add
      stochastic start (n + 1) 1]
    rw [hprefix, PMF.pure_bind]
    rw [hchanceHistoryEq]
    have hchanceNonterminal :=
      chanceState_not_terminal G rootPayoff source hnonterminal
        jointAction
    rw [Arena.stochasticHistoryPMFFrom_succ_of_not_terminal
      stochastic
      ⟨chanceState G source hnonterminal jointAction, chancePath⟩
      0 hchanceNonterminal]
    change
      (G.transition source.1 jointAction).bind
          (fun nextWorld => PMF.pure (targetEndpoint nextWorld)) =
        (G.transition source.1 jointAction).map targetEndpoint
    rfl
  · intro nextWorld
    rfl

/-- Serializer macro boundaries are terminal exactly when their FOSG macro
states are terminal. -/
theorem boundary_isTerminal_iff
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U)
    (source : G.HistoryState) :
    (game G rootPayoff).isTerminal (boundary G source) ↔
      G.isTerminal source.1 := by
  by_cases hterminal : G.isTerminal source.1
  · rw [boundary_of_terminal G source hterminal]
    constructor
    · intro _
      exact hterminal
    · intro _
      exact ⟨fun action => nomatch action⟩
  · rw [boundary_of_not_terminal G source hterminal]
    constructor
    · intro hserializedTerminal
      have hnotEmptyJoint :
          ¬ IsEmpty (G.JointAction source.1) := by
        intro hempty
        exact hterminal ((G.terminal_iff source.1).mpr hempty)
      obtain ⟨jointAction⟩ :=
        not_isEmpty_iff.mp hnotEmptyJoint
      exact False.elim
        (hserializedTerminal.false
          (jointAction (0 : Fin (n + 1))))
    · intro h
      exact (hterminal h).elim

/-- The macro policy uses the compiled observed EFG's declared chance kernel
at every chance history. -/
theorem macroPolicy_chanceConsistent
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (source : G.HistoryState)
    (jointAction : G.JointAction source.1) :
    (observedChanceGame G D rootPayoff sourceDeclaredRoot).ChanceConsistent
      (macroPolicy G rootPayoff source jointAction) := by
  intro history hnonterminal hmover
  rcases history with ⟨state, path⟩
  cases state with
  | root =>
      rfl
  | terminal macroHistory hterminal =>
      exfalso
      apply hnonterminal
      exact ⟨fun action => nomatch action⟩
  | player macroHistory hmacroNonterminal count hcount collected =>
      simp [observedChanceGame, game, mover] at hmover
  | chance macroHistory hmacroNonterminal action =>
      rfl

/-- The concrete compiler's coupling-based probabilistic weak simulation. -/
noncomputable def probabilisticWeakSimulation
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop) :
    KernelArena.ProbabilisticWeakSimulation
      G.historyKernelArena
      (game G rootPayoff).toArena
      (game G rootPayoff).init
      (observedChanceGame G D rootPayoff
        sourceDeclaredRoot).ChanceConsistent where
  Rel := Rel G
  match_action := by
    intro source target hrelated jointAction
    obtain ⟨targetEndpoint, htargetLaw, htargetBoundary⟩ :=
      exists_macroExecutionLaw G rootPayoff source jointAction
        target hrelated
    let sourceEndpoint : G.WorldState → G.HistoryState :=
      fun nextWorld =>
        ⟨nextWorld,
          FOSG.History.snoc source.2 jointAction nextWorld⟩
    let coupling :
        PMF
          (G.HistoryState ×
            (game G rootPayoff).toArena.HistoryFrom
              (game G rootPayoff).init) :=
      (G.transition source.1 jointAction).map fun nextWorld =>
        (sourceEndpoint nextWorld, targetEndpoint nextWorld)
    refine
      ⟨macroPolicy G rootPayoff source jointAction,
        n + 2, by omega,
        macroPolicy_chanceConsistent G D rootPayoff sourceDeclaredRoot
          source jointAction,
        coupling, ?_, ?_, ?_⟩
    · calc
        coupling.map Prod.fst =
            (G.transition source.1 jointAction).map
              sourceEndpoint := by
                rw [PMF.map_comp]
                rfl
        _ = G.historyKernelArena.next source jointAction := rfl
    · calc
        coupling.map Prod.snd =
            (G.transition source.1 jointAction).map
              targetEndpoint := by
                rw [PMF.map_comp]
                rfl
        _ = (game G rootPayoff).toArena.stochasticHistoryPMFFrom
            (macroPolicy G rootPayoff source jointAction)
            target (n + 2) :=
          htargetLaw.symm
    · intro pair hpair
      obtain ⟨nextWorld, _, hmap⟩ :=
        (PMF.mem_support_map_iff
          (p := G.transition source.1 jointAction)
          (f := fun nextWorld =>
            (sourceEndpoint nextWorld, targetEndpoint nextWorld))
          (b := pair)).mp hpair
      subst pair
      exact htargetBoundary nextWorld
  terminal_iff := by
    intro source target hrelated
    calc
      IsEmpty (G.historyKernelArena.Action source) ↔
          G.isTerminal source.1 :=
        G.historyKernelArena_isTerminal_iff source
      _ ↔ (game G rootPayoff).isTerminal (boundary G source) :=
        (boundary_isTerminal_iff G rootPayoff source).symm
      _ ↔ (game G rootPayoff).isTerminal target.1 := by
        rw [hrelated]

/-- The compiled EFG viewed as a stochastic arena of admissible macro
executions.

An action packages a positive-length chance-consistent serialized policy and
its micro-step horizon.  The transition kernel is its exact endpoint law. -/
noncomputable def macroExecutionKernelArena
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop) :
    KernelArena :=
  KernelArena.executionKernelArena
    (game G rootPayoff).toArena
    (game G rootPayoff).init
    (observedChanceGame G D rootPayoff
      sourceDeclaredRoot).ChanceConsistent

/-- The positive serialized execution implementing one concrete FOSG joint
action from a related macro boundary. -/
noncomputable def macroExecutionAction
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (source : G.HistoryState)
    (jointAction : G.JointAction source.1)
    (target :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init)
    (htarget :
      ¬ (game G rootPayoff).isTerminal target.1) :
    (macroExecutionKernelArena G D rootPayoff
      sourceDeclaredRoot).Action target where
  nonterminal := htarget
  policy := macroPolicy G rootPayoff source jointAction
  fuel := n + 2
  positive := by omega
  admissible :=
    macroPolicy_chanceConsistent G D rootPayoff sourceDeclaredRoot
      source jointAction

/-- Nonemptiness of the compiled macro-action type certifies that its
underlying serialized boundary is nonterminal. -/
noncomputable def macroTargetNonterminal
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (target :
      (macroExecutionKernelArena G D rootPayoff
        sourceDeclaredRoot).State)
    (htarget :
      ¬ IsEmpty
        ((macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).Action target)) :
    ¬ (game G rootPayoff).isTerminal target.1 :=
  (Classical.choice (not_isEmpty_iff.mp htarget)).nonterminal

/-- Compile a randomized FOSG macro policy to a randomized policy on the
serialized EFG's macro-execution Arena.

At a genuine macro boundary the unique related FOSG history is recovered and
each joint action is mapped to its canonical positive `n + 2`-step execution.
At unrelated states the policy returns an arbitrary already-certified action;
that branch is unreachable from related initial states and contributes to no
transfer theorem. -/
noncomputable def serializedMacroPolicy
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (sourcePolicy : G.historyKernelArena.Policy) :
    (macroExecutionKernelArena G D rootPayoff
      sourceDeclaredRoot).Policy :=
  by
  classical
  exact fun target htarget =>
    if hexists : ∃ source : G.HistoryState, Rel G source target then
      let source := Classical.choose hexists
      let hrelated : Rel G source target :=
        Classical.choose_spec hexists
      have hsource :
          ¬ IsEmpty (G.historyKernelArena.Action source) := by
        intro hterminal
        exact
          (macroTargetNonterminal G D rootPayoff sourceDeclaredRoot
            target htarget)
            (((probabilisticWeakSimulation G D rootPayoff
              sourceDeclaredRoot).terminal_iff hrelated).mp hterminal)
      (sourcePolicy source hsource).map fun jointAction =>
        macroExecutionAction G D rootPayoff sourceDeclaredRoot
          source jointAction target
            (macroTargetNonterminal G D rootPayoff
              sourceDeclaredRoot target htarget)
    else
      PMF.pure (Classical.choice (not_isEmpty_iff.mp htarget))

/-- At a related boundary, the compiled macro policy is exactly the
pushforward of the source joint-action law through canonical serialized
executions. -/
theorem serializedMacroPolicy_eq_map
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (sourcePolicy : G.historyKernelArena.Policy)
    {source : G.HistoryState}
    {target :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init}
    (hrelated : Rel G source target)
    (hsource :
      ¬ IsEmpty (G.historyKernelArena.Action source))
    (htarget :
      ¬ IsEmpty
        ((macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).Action target)) :
    serializedMacroPolicy G D rootPayoff sourceDeclaredRoot
        sourcePolicy target htarget =
      (sourcePolicy source hsource).map fun jointAction =>
        macroExecutionAction G D rootPayoff sourceDeclaredRoot
          source jointAction target
            (macroTargetNonterminal G D rootPayoff
              sourceDeclaredRoot target htarget) := by
  classical
  rw [serializedMacroPolicy]
  split
  · rename_i hexists
    let chosen := Classical.choose hexists
    have hchosenRelated : Rel G chosen target :=
      Classical.choose_spec hexists
    have hchosen : chosen = source :=
      Rel.left_unique G hchosenRelated hrelated
    change Classical.choose hexists = source at hchosen
    subst source
    rfl
  · rename_i hmissing
    exact (hmissing ⟨source, hrelated⟩).elim


end ExtensiveGame.FOSG.Sequentialization
