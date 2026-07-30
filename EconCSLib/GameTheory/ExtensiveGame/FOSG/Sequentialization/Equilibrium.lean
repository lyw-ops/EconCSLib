/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.Witness

/-!
# EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.Equilibrium

Finite-horizon behavioral Nash and macro-Nash on presentation-designated continuations transfer.
-/

namespace ExtensiveGame.FOSG.Sequentialization

universe uU

variable {n : ℕ} {U : Type uU}
  (G : FOSG (Fin (n + 1)) U)

/-! ### Finite-horizon behavioral equilibrium transfer -/

/-- The initialized finite-horizon FOSG behavioral game form.

An outcome is the complete PMF of optional terminal payoffs: `none` records
that the finite horizon ended before termination. Expected utility, risk
measures, and distributional preferences can all be supplied externally. -/
noncomputable def sourceBehavioralGameForm
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (horizon : Nat) :
    GameForm (Fin (n + 1)) where
  Strategy := D.BehavioralStrategy
  Outcome := PMF (Option (Fin (n + 1) → U))
  outcome profile :=
    (initializedSourceStateLaw G
      (D.behavioralHistoryPolicy profile) horizon).map
        G.stoppedPayoffAtHistory

/-- The initialized finite-horizon behavioral game form of the genuinely
micro-executed serialized observed EFG. -/
noncomputable def serializedBehavioralGameForm
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (horizon : Nat) :
    GameForm (Fin (n + 1)) where
  Strategy :=
    (observedChanceGame G D rootPayoff
      sourceDeclaredRoot).observed.BehavioralStrategy
  Outcome := PMF (Option (Fin (n + 1) → U))
  outcome profile :=
    (initializedBehavioralTargetMicroStateLaw G D rootPayoff
      sourceDeclaredRoot profile horizon).map
        (serializedStoppedPayoffAtHistory G rootPayoff)

/-- Exact finite-horizon game-form isomorphism between FOSG behavioral play
and genuine serialized observed-EFG behavioral play. -/
noncomputable def behavioralGameFormIso
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (horizon : Nat) :
    (sourceBehavioralGameForm G D horizon).Iso
      (serializedBehavioralGameForm G D rootPayoff
        sourceDeclaredRoot horizon) where
  strategyEquiv := fun _ => Equiv.refl _
  outcomeEquiv := Equiv.refl _
  map_outcome := by
    intro profile
    exact
      initializedBehavioralMicroPayoffLaw_eq G D rootPayoff
        sourceDeclaredRoot profile horizon

/-- Finite-horizon behavioral Nash equilibrium transfers in both directions
between the FOSG and its genuinely micro-executed serialized observed EFG.

The utility functional may inspect the entire optional terminal-payoff
distribution; an expected-utility interpretation is one specialization. -/
theorem behavioralIsNash_iff
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    [DecidableEq (Fin (n + 1))]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (horizon : Nat)
    {V : Type*} [Preorder V]
    (utility :
      PMF (Option (Fin (n + 1) → U)) →
        Fin (n + 1) → V)
    (profile : D.BehavioralProfile) :
    (sourceBehavioralGameForm G D horizon).IsNash
        utility profile ↔
      (serializedBehavioralGameForm G D rootPayoff
        sourceDeclaredRoot horizon).IsNash
          utility
          ((behavioralGameFormIso G D rootPayoff
            sourceDeclaredRoot horizon).mapProfile profile) := by
  exact
    (behavioralGameFormIso G D rootPayoff
      sourceDeclaredRoot horizon).isNash_iff
        (by
          intro outcome i
          rfl)
        profile

/-- Terminality decision instance specialized to the compiled observed chance
game. -/
noncomputable instance instObservedDecidableIsTerminal
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop) :
    (state :
      (observedChanceGame G D rootPayoff
        sourceDeclaredRoot).observed.base.State) →
      Decidable
        ((observedChanceGame G D rootPayoff
          sourceDeclaredRoot).observed.base.isTerminal state) :=
  instDecidableIsTerminal G rootPayoff

/-- The concrete finite-player sequential compiler satisfies the complete
`FOSG.WeakSerialization` interface. -/
noncomputable def weakSerialization
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop) :
    G.WeakSerialization
      (observedChanceGame G D rootPayoff sourceDeclaredRoot) where
  simulation :=
    probabilisticWeakSimulation G D rootPayoff sourceDeclaredRoot
  match_init := by
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
    refine
      ⟨initialPolicy G rootPayoff, 1,
        initialPolicy_chanceConsistent G D rootPayoff
          sourceDeclaredRoot,
        coupling, ?_, ?_, ?_⟩
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
  observationMap := fun _ privateObservation => some privateObservation
  observationMap_injective := by
    intro i left right heq
    exact Option.some.inj heq
  map_observe := by
    intro i source target hrelated
    change
      some (G.privateObservations i source.2) =
        privateView G i target.1
    change Rel G source target at hrelated
    rw [hrelated]
    by_cases hterminal : G.isTerminal source.1
    · simp [boundary, hterminal, privateView]
    · simp [boundary, hterminal, privateView]
  publicMap := some
  publicMap_injective := by
    intro left right heq
    exact Option.some.inj heq
  map_publicObserve := by
    intro source target hrelated
    change
      some (G.publicObservations source.2) =
        publicView G target.1
    change Rel G source target at hrelated
    rw [hrelated]
    by_cases hterminal : G.isTerminal source.1
    · simp [boundary, hterminal, publicView]
    · simp [boundary, hterminal, publicView]
  map_publicOf := by
    intro i privateObservation
    rfl
  map_terminalPayoff := by
    intro source target hrelated hterminal
    rw [hrelated]
    simp [observedChanceGame, game, boundary, hterminal]
  IsDeclaredMacroRoot := sourceDeclaredRoot
  map_declaredMacroRoot := by
    intro source target hrelated
    change
      sourceDeclaredRoot source ↔
        isDesignatedContinuationRoot G sourceDeclaredRoot target.1
    change Rel G source target at hrelated
    rw [hrelated]
    by_cases hterminal : G.isTerminal source.1
    · simp [isDesignatedContinuationRoot, boundary, hterminal]
    · simp [isDesignatedContinuationRoot, boundary, hterminal]

/-- The concrete sequential compiler gives a progressing weak simulation on
all positive-probability realized paths. -/
theorem weakSerialization_progressing
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop) :
    (weakSerialization G D rootPayoff sourceDeclaredRoot).toSupportWeakSimulation.Progressing :=
  (weakSerialization G D rootPayoff
    sourceDeclaredRoot).toSupportWeakSimulation_progressing

end ExtensiveGame.FOSG.Sequentialization
