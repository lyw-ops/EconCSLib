/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.Trajectory

/-!
# EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.Witness

Initialization laws and the complete weak-serialization witness.
-/

namespace ExtensiveGame.FOSG.Sequentialization

universe uU

variable {n : ℕ} {U : Type uU}
  (G : FOSG (Fin (n + 1)) U)

/-! ### Initial distribution and complete serialization witness -/

/-- Chance-consistent policy used only for the synthetic initial-root step. -/
noncomputable def initialPolicy
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U) :
    (game G rootPayoff).toArena.StochasticHistoryPolicy
      (game G rootPayoff).init :=
  fun history hnonterminal => by
    rcases history with ⟨state, path⟩
    cases state with
    | root =>
        exact G.init
    | terminal macroHistory hterminal =>
        exfalso
        apply hnonterminal
        exact ⟨fun action => nomatch action⟩
    | player macroHistory hmacroNonterminal count hcount collected =>
        exact PMF.pure
          (Classical.choice (not_isEmpty_iff.mp hnonterminal))
    | chance macroHistory hmacroNonterminal action =>
        exact G.transition macroHistory.1 action

/-- The initial policy uses exactly the compiled root and transition chance
kernels. -/
theorem initialPolicy_chanceConsistent
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop) :
    (observedChanceGame G D rootPayoff sourceDeclaredRoot).ChanceConsistent
      (initialPolicy G rootPayoff) := by
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
      simp [observedChanceGameCore, game, mover] at hmover
  | chance macroHistory hmacroNonterminal action =>
      rfl

/-- The synthetic initial root is nonterminal because an initial `PMF` has
nonempty support. -/
theorem root_not_terminal
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U) :
    ¬ (game G rootPayoff).isTerminal .root := by
  intro hterminal
  obtain ⟨world, _⟩ := G.init.support_nonempty
  exact hterminal.false world

/-- Exact one-step target law from the synthetic initial root. -/
theorem initialExecutionLaw
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U) :
    (game G rootPayoff).toArena.stochasticHistoryPMFFrom
        (initialPolicy G rootPayoff)
        (Arena.HistoryFrom.nil
          (game G rootPayoff).toArena (game G rootPayoff).init)
        1 =
      G.init.map (fun world =>
        (⟨boundary G
            ⟨world, FOSG.History.initial world⟩,
          (Arena.History.nil :
            (game G rootPayoff).toArena.History
              (game G rootPayoff).init
              (game G rootPayoff).init).snoc world⟩ :
          (game G rootPayoff).toArena.HistoryFrom
            (game G rootPayoff).init)) := by
  rw [Arena.stochasticHistoryPMFFrom_succ_of_not_terminal
    (initialPolicy G rootPayoff)
    (Arena.HistoryFrom.nil
      (game G rootPayoff).toArena (game G rootPayoff).init)
    0 (root_not_terminal G rootPayoff)]
  change
    G.init.bind
        (fun world =>
          PMF.pure
            (⟨boundary G
                ⟨world, FOSG.History.initial world⟩,
              (Arena.History.nil :
                (game G rootPayoff).toArena.History
                  (game G rootPayoff).init
                  (game G rootPayoff).init).snoc world⟩ :
              (game G rootPayoff).toArena.HistoryFrom
                (game G rootPayoff).init)) =
      G.init.map (fun world =>
        (⟨boundary G
            ⟨world, FOSG.History.initial world⟩,
          (Arena.History.nil :
            (game G rootPayoff).toArena.History
              (game G rootPayoff).init
              (game G rootPayoff).init).snoc world⟩ :
          (game G rootPayoff).toArena.HistoryFrom
            (game G rootPayoff).init))
  rfl

/-- The genuine serialized behavioral policy and the initialization-only
policy have exactly the same one-step law from the synthetic root. -/
theorem behavioralInitialExecutionLaw
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (profile : D.BehavioralProfile) :
    (game G rootPayoff).toArena.stochasticHistoryPMFFrom
        (serializedBehavioralHistoryPolicy G D rootPayoff
          sourceDeclaredRoot profile)
        (Arena.HistoryFrom.nil
          (game G rootPayoff).toArena
          (game G rootPayoff).init)
        1 =
      (game G rootPayoff).toArena.stochasticHistoryPMFFrom
        (initialPolicy G rootPayoff)
        (Arena.HistoryFrom.nil
          (game G rootPayoff).toArena
          (game G rootPayoff).init)
        1 := by
  have hroot := root_not_terminal G rootPayoff
  rw [Arena.stochasticHistoryPMFFrom_succ_of_not_terminal
    (serializedBehavioralHistoryPolicy G D rootPayoff
      sourceDeclaredRoot profile)
    (Arena.HistoryFrom.nil
      (game G rootPayoff).toArena
      (game G rootPayoff).init)
    0 hroot]
  rw [Arena.stochasticHistoryPMFFrom_succ_of_not_terminal
    (initialPolicy G rootPayoff)
    (Arena.HistoryFrom.nil
      (game G rootPayoff).toArena
      (game G rootPayoff).init)
    0 hroot]
  rw [serializedBehavioralHistoryPolicy_root G D rootPayoff
    sourceDeclaredRoot profile hroot]
  change G.init.bind _ = G.init.bind _
  apply congrArg (PMF.bind G.init)
  funext world
  rfl

/-- Exact coupling of the random initial augmented FOSG history and the
serialized EFG history after its synthetic root chance step. -/
theorem initialBoundaryCoupling
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U) :
    PMF.RelCoupling (Rel G)
      G.initialHistoryKernel
      ((game G rootPayoff).toArena.stochasticHistoryPMFFrom
        (initialPolicy G rootPayoff)
        (Arena.HistoryFrom.nil
          (game G rootPayoff).toArena
          (game G rootPayoff).init)
        1) := by
  let sourceInitial : G.WorldState → G.HistoryState :=
    fun world => ⟨world, FOSG.History.initial world⟩
  let targetInitial :
      G.WorldState →
        (game G rootPayoff).toArena.HistoryFrom
          (game G rootPayoff).init :=
    fun world =>
      ⟨boundary G (sourceInitial world),
        (Arena.History.nil :
          (game G rootPayoff).toArena.History
            (game G rootPayoff).init
            (game G rootPayoff).init).snoc world⟩
  let coupling :
      PMF
        (G.HistoryState ×
          (game G rootPayoff).toArena.HistoryFrom
            (game G rootPayoff).init) :=
    G.init.map fun world =>
      (sourceInitial world, targetInitial world)
  refine ⟨coupling, ?_, ?_, ?_⟩
  · calc
      coupling.map Prod.fst =
          G.init.map sourceInitial := by
            rw [PMF.map_comp]
            rfl
      _ = G.initialHistoryKernel := rfl
  · calc
      coupling.map Prod.snd =
          G.init.map targetInitial := by
            rw [PMF.map_comp]
            rfl
      _ = (game G rootPayoff).toArena.stochasticHistoryPMFFrom
          (initialPolicy G rootPayoff)
          (Arena.HistoryFrom.nil
            (game G rootPayoff).toArena
            (game G rootPayoff).init)
          1 :=
        (initialExecutionLaw G rootPayoff).symm
  · intro pair hpair
    obtain ⟨world, _, hmap⟩ :=
      (PMF.mem_support_map_iff
        (p := G.init)
        (f := fun world =>
          (sourceInitial world, targetInitial world))
        (b := pair)).mp hpair
    subst pair
    rfl

/-- Source endpoint law after random initialization and at most `horizon`
FOSG macro transitions. -/
noncomputable def initializedSourceStateLaw
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (sourcePolicy : G.historyKernelArena.Policy)
    (horizon : Nat) :
    PMF G.HistoryState :=
  G.initialHistoryKernel.bind
    (G.historyKernelArena.stateLawFrom sourcePolicy horizon)

/-- Serialized endpoint law after its synthetic root chance step and at most
`horizon` compiled macro executions. -/
noncomputable def initializedTargetStateLaw
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (sourcePolicy : G.historyKernelArena.Policy)
    (horizon : Nat) :
    PMF
      ((game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init) :=
  ((game G rootPayoff).toArena.stochasticHistoryPMFFrom
      (initialPolicy G rootPayoff)
      (Arena.HistoryFrom.nil
        (game G rootPayoff).toArena
        (game G rootPayoff).init)
      1).bind
    ((macroExecutionKernelArena G D rootPayoff
      sourceDeclaredRoot).stateLawFrom
      (serializedMacroPolicy G D rootPayoff sourceDeclaredRoot
        sourcePolicy)
      horizon)

/-- Actual micro-step endpoint law of the genuine serialized observed-EFG
behavioral profile, including the synthetic initial chance step.

One source macro transition consumes `n + 2` target micro steps. -/
noncomputable def initializedBehavioralTargetMicroStateLaw
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (profile : D.BehavioralProfile)
    (horizon : Nat) :
    PMF
      ((game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init) :=
  (game G rootPayoff).toArena.stochasticHistoryPMFFrom
    (serializedBehavioralHistoryPolicy G D rootPayoff
      sourceDeclaredRoot profile)
    (Arena.HistoryFrom.nil
      (game G rootPayoff).toArena
      (game G rootPayoff).init)
    (1 + horizon * (n + 2))

/-- The actual initialized micro-step law of the target behavioral profile is
exactly the initialized macro-controller law. -/
theorem initializedBehavioralTargetMicroStateLaw_eq
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (profile : D.BehavioralProfile)
    (horizon : Nat) :
    initializedBehavioralTargetMicroStateLaw G D rootPayoff
        sourceDeclaredRoot profile horizon =
      initializedTargetStateLaw G D rootPayoff sourceDeclaredRoot
        (D.behavioralHistoryPolicy profile) horizon := by
  rw [initializedBehavioralTargetMicroStateLaw]
  rw [Arena.stochasticHistoryPMFFrom_add]
  rw [behavioralInitialExecutionLaw G D rootPayoff
    sourceDeclaredRoot profile]
  rw [initializedTargetStateLaw]
  apply PMF.bind_congr_support
  intro target htarget
  obtain ⟨source, _, hrelated⟩ :=
    PMF.RelCoupling.exists_left_of_mem_support_right
      (initialBoundaryCoupling G rootPayoff) htarget
  exact
    serializedBehavioralMicroStateLaw_eq_macro G D rootPayoff
      sourceDeclaredRoot profile hrelated horizon

/-- Full finite-horizon endpoint coupling, including the random initial world
and all compiled macro executions. -/
theorem initializedStateLawCoupling
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (sourcePolicy : G.historyKernelArena.Policy)
    (horizon : Nat) :
    PMF.RelCoupling (Rel G)
      (initializedSourceStateLaw G sourcePolicy horizon)
      (initializedTargetStateLaw G D rootPayoff sourceDeclaredRoot
        sourcePolicy horizon) := by
  exact
    (initialBoundaryCoupling G rootPayoff).bind
      (fun _ _ hrelated =>
        serializedMacroStateLawCoupling G D rootPayoff
          sourceDeclaredRoot sourcePolicy hrelated horizon)

/-- Exact equality of complete initialized finite-horizon optional
terminal-payoff laws. -/
theorem initializedPayoffLaw_eq
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (sourcePolicy : G.historyKernelArena.Policy)
    (horizon : Nat) :
    (initializedSourceStateLaw G sourcePolicy horizon).map
        G.stoppedPayoffAtHistory =
      (initializedTargetStateLaw G D rootPayoff sourceDeclaredRoot
        sourcePolicy horizon).map
          (serializedStoppedPayoffAtHistory G rootPayoff) := by
  exact
    (initializedStateLawCoupling G D rootPayoff sourceDeclaredRoot
      sourcePolicy horizon).map_eq
        (fun sourceState targetHistory hrelated =>
          (stoppedPayoff_eq_of_rel G rootPayoff sourceState
            targetHistory hrelated).symm)

/-- Every scalar or structured utility computed from the optional terminal
payoff has the same initialized finite-horizon law in both representations.

Consequently any expectation functional defined on this common PMF yields
equal expected utility without further simulation reasoning. -/
theorem initializedUtilityLaw_eq
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (sourcePolicy : G.historyKernelArena.Policy)
    (horizon : Nat)
    {V : Type*}
    (utility : Option (Fin (n + 1) → U) → V) :
    (initializedSourceStateLaw G sourcePolicy horizon).map
        (fun state => utility (G.stoppedPayoffAtHistory state)) =
      (initializedTargetStateLaw G D rootPayoff sourceDeclaredRoot
        sourcePolicy horizon).map
          (fun history =>
            utility
              (serializedStoppedPayoffAtHistory
                G rootPayoff history)) := by
  exact
    (initializedStateLawCoupling G D rootPayoff sourceDeclaredRoot
      sourcePolicy horizon).map_eq
        (fun sourceState targetHistory hrelated =>
          congrArg utility
            (stoppedPayoff_eq_of_rel G rootPayoff sourceState
              targetHistory hrelated).symm)

/-- Information-indexed behavioral profiles preserve every initialized
finite-horizon derived-utility law under serialization. -/
theorem initializedBehavioralUtilityLaw_eq
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (profile : D.BehavioralProfile)
    (horizon : Nat)
    {V : Type*}
    (utility : Option (Fin (n + 1) → U) → V) :
    (initializedSourceStateLaw G
        (D.behavioralHistoryPolicy profile) horizon).map
          (fun state =>
            utility (G.stoppedPayoffAtHistory state)) =
      (initializedTargetStateLaw G D rootPayoff sourceDeclaredRoot
        (D.behavioralHistoryPolicy profile) horizon).map
          (fun history =>
            utility
              (serializedStoppedPayoffAtHistory
                G rootPayoff history)) :=
  initializedUtilityLaw_eq G D rootPayoff sourceDeclaredRoot
    (D.behavioralHistoryPolicy profile) horizon utility

/-- Source behavioral play and genuine target observed-EFG behavioral play
have exactly the same initialized finite-horizon optional terminal-payoff law.
-/
theorem initializedBehavioralMicroPayoffLaw_eq
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (profile : D.BehavioralProfile)
    (horizon : Nat) :
    (initializedSourceStateLaw G
        (D.behavioralHistoryPolicy profile) horizon).map
          G.stoppedPayoffAtHistory =
      (initializedBehavioralTargetMicroStateLaw G D rootPayoff
        sourceDeclaredRoot profile horizon).map
          (serializedStoppedPayoffAtHistory G rootPayoff) := by
  rw [initializedBehavioralTargetMicroStateLaw_eq G D rootPayoff
    sourceDeclaredRoot profile horizon]
  exact
    initializedPayoffLaw_eq G D rootPayoff sourceDeclaredRoot
      (D.behavioralHistoryPolicy profile) horizon

/-- Every utility computed from the optional terminal payoff has the same law
under source behavioral play and genuine target micro-step behavioral play. -/
theorem initializedBehavioralMicroUtilityLaw_eq
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (profile : D.BehavioralProfile)
    (horizon : Nat)
    {V : Type*}
    (utility : Option (Fin (n + 1) → U) → V) :
    (initializedSourceStateLaw G
        (D.behavioralHistoryPolicy profile) horizon).map
          (fun state =>
            utility (G.stoppedPayoffAtHistory state)) =
      (initializedBehavioralTargetMicroStateLaw G D rootPayoff
        sourceDeclaredRoot profile horizon).map
          (fun history =>
            utility
              (serializedStoppedPayoffAtHistory
                G rootPayoff history)) := by
  rw [initializedBehavioralTargetMicroStateLaw_eq G D rootPayoff
    sourceDeclaredRoot profile horizon]
  exact
    initializedBehavioralUtilityLaw_eq G D rootPayoff
      sourceDeclaredRoot profile horizon utility


end ExtensiveGame.FOSG.Sequentialization
