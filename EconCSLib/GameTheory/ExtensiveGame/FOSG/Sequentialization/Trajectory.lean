/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.MacroLaw

/-!
# EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.Trajectory

Policy compilation, finite-horizon coupling, and payoff-law equality.
-/

namespace ExtensiveGame.FOSG.Sequentialization

universe uU

variable {n : ℕ} {U : Type uU}
  (G : FOSG (Fin (n + 1)) U)

/-- The concrete weak serializer is an exact kernel simulation when observed
at macro boundaries.

This repackaging is what permits generic finite-horizon coupling theorems to
iterate the compiler's one-step correctness proof. -/
noncomputable def macroKernelSimulation
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop) :
    G.historyKernelArena.Simulation
      (macroExecutionKernelArena G D rootPayoff sourceDeclaredRoot) :=
  (probabilisticWeakSimulation G D rootPayoff
    sourceDeclaredRoot).toKernelSimulation

/-- A canonical serialized macro action has an endpoint law exactly coupled
to the corresponding FOSG successor law. -/
theorem macroExecutionAction_coupling
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
      ¬ (game G rootPayoff).isTerminal target.1)
    (hrelated : Rel G source target) :
    PMF.RelCoupling (Rel G)
      (G.historyKernelArena.next source jointAction)
      ((macroExecutionKernelArena G D rootPayoff
        sourceDeclaredRoot).next target
          (macroExecutionAction G D rootPayoff sourceDeclaredRoot
            source jointAction target htarget)) := by
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
  refine ⟨coupling, ?_, ?_, ?_⟩
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
      _ = (macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).next target
            (macroExecutionAction G D rootPayoff sourceDeclaredRoot
              source jointAction target htarget) := rfl
  · intro pair hpair
    obtain ⟨nextWorld, _, hmap⟩ :=
      (PMF.mem_support_map_iff
        (p := G.transition source.1 jointAction)
        (f := fun nextWorld =>
          (sourceEndpoint nextWorld, targetEndpoint nextWorld))
        (b := pair)).mp hpair
    subst pair
    exact htargetBoundary nextWorld

/-- The concrete policy compiler supplies the `PolicyMatch` required by the
generic finite-horizon trajectory theorems. -/
theorem serializedMacroPolicy_match
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (sourcePolicy : G.historyKernelArena.Policy) :
    (macroKernelSimulation G D rootPayoff sourceDeclaredRoot).PolicyMatch
      sourcePolicy
      (serializedMacroPolicy G D rootPayoff sourceDeclaredRoot
        sourcePolicy) where
  terminal_iff := by
    intro source target hrelated
    exact
      (probabilisticWeakSimulation G D rootPayoff
        sourceDeclaredRoot).toKernelSimulation_terminal_iff hrelated
  actionCoupling := by
    intro source target hrelated hsource htarget
    rw [serializedMacroPolicy_eq_map G D rootPayoff
      sourceDeclaredRoot sourcePolicy hrelated hsource htarget]
    let targetNonterminal :=
      macroTargetNonterminal G D rootPayoff sourceDeclaredRoot
        target htarget
    let actionMap :
        G.historyKernelArena.Action source →
          (macroExecutionKernelArena G D rootPayoff
            sourceDeclaredRoot).Action target :=
      fun jointAction =>
        macroExecutionAction G D rootPayoff sourceDeclaredRoot
          source jointAction target targetNonterminal
    let coupling :=
      (sourcePolicy source hsource).map fun jointAction =>
        (jointAction, actionMap jointAction)
    refine ⟨coupling, ?_, ?_, ?_⟩
    · calc
        coupling.map Prod.fst =
            (sourcePolicy source hsource).map id := by
              rw [PMF.map_comp]
              rfl
        _ = sourcePolicy source hsource :=
          PMF.map_id _
    · calc
        coupling.map Prod.snd =
            (sourcePolicy source hsource).map actionMap := by
              rw [PMF.map_comp]
              rfl
        _ = (sourcePolicy source hsource).map
            (fun jointAction =>
              macroExecutionAction G D rootPayoff
                sourceDeclaredRoot source jointAction target
                  (macroTargetNonterminal G D rootPayoff
                    sourceDeclaredRoot target htarget)) := rfl
    · intro pair hpair
      obtain ⟨jointAction, _, hmap⟩ :=
        (PMF.mem_support_map_iff
          (p := sourcePolicy source hsource)
          (f := fun jointAction =>
            (jointAction, actionMap jointAction))
          (b := pair)).mp hpair
      subst pair
      exact
        macroExecutionAction_coupling G D rootPayoff
          sourceDeclaredRoot source jointAction target
            targetNonterminal hrelated

/-- Compile an information-indexed behavioral profile all the way to the
serialized EFG's terminal-aware macro policy. -/
noncomputable def serializedBehavioralMacroPolicy
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (profile : D.BehavioralProfile) :
    (macroExecutionKernelArena G D rootPayoff
      sourceDeclaredRoot).Policy :=
  serializedMacroPolicy G D rootPayoff sourceDeclaredRoot
    (D.behavioralHistoryPolicy profile)

/-- The genuine target observed-EFG behavioral policy realizes exactly one
step of the compiled macro policy at every related nonterminal boundary. -/
theorem serializedBehavioralExecution_eq_macroStepLaw
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
    (hrelated : Rel G source target)
    (htarget :
      ¬ IsEmpty
        ((macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).Action target)) :
    (game G rootPayoff).toArena.stochasticHistoryPMFFrom
        (serializedBehavioralHistoryPolicy G D rootPayoff
          sourceDeclaredRoot profile)
        target (n + 2) =
      (macroExecutionKernelArena G D rootPayoff
        sourceDeclaredRoot).stepLaw
          (serializedBehavioralMacroPolicy G D rootPayoff
            sourceDeclaredRoot profile)
          target htarget := by
  rw [serializedBehavioralExecution_eq_jointActionLaw_bind_macro
    G D rootPayoff sourceDeclaredRoot profile source hsource target
    hrelated]
  have hsourceActions :
      ¬ IsEmpty (G.historyKernelArena.Action source) := by
    rw [G.historyKernelArena_isTerminal_iff]
    exact hsource
  rw [KernelArena.stepLaw, serializedBehavioralMacroPolicy]
  rw [serializedMacroPolicy_eq_map G D rootPayoff sourceDeclaredRoot
    (D.behavioralHistoryPolicy profile) hrelated hsourceActions
    htarget]
  rw [PMF.bind_map]
  change
    (D.jointActionLaw profile source hsource).bind _ =
      (D.jointActionLaw profile source hsource).bind _
  apply congrArg
    (PMF.bind (D.jointActionLaw profile source hsource))
  funext jointAction
  rfl

/-- The behavioral-profile compiler satisfies exact terminal-aware policy
matching. -/
theorem serializedBehavioralMacroPolicy_match
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (profile : D.BehavioralProfile) :
    (macroKernelSimulation G D rootPayoff sourceDeclaredRoot).PolicyMatch
      (D.behavioralHistoryPolicy profile)
      (serializedBehavioralMacroPolicy G D rootPayoff
        sourceDeclaredRoot profile) :=
  serializedMacroPolicy_match G D rootPayoff sourceDeclaredRoot
    (D.behavioralHistoryPolicy profile)

/-- Continuous execution of the genuine serialized observed-EFG behavioral
policy for `horizon * (n + 2)` micro steps is exactly the stopped
`horizon`-step law of its compiled macro policy.

The induction uses the one-block realization theorem at every related
boundary. Coupling support supplies the related source witness needed for the
next block, so the result includes early terminal stopping. -/
theorem serializedBehavioralMicroStateLaw_eq_macro
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (profile : D.BehavioralProfile)
    {source : G.HistoryState}
    {target :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init}
    (hrelated : Rel G source target) :
    ∀ horizon : ℕ,
      (game G rootPayoff).toArena.stochasticHistoryPMFFrom
          (serializedBehavioralHistoryPolicy G D rootPayoff
            sourceDeclaredRoot profile)
          target (horizon * (n + 2)) =
        (macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).stateLawFrom
            (serializedBehavioralMacroPolicy G D rootPayoff
              sourceDeclaredRoot profile)
            horizon target := by
  intro horizon
  induction horizon generalizing source target with
  | zero =>
      simp [KernelArena.stateLawFrom]
      rfl
  | succ horizon ih =>
      by_cases hsourceTerminal : G.isTerminal source.1
      · have hsourceActions :
            IsEmpty (G.historyKernelArena.Action source) :=
          (G.historyKernelArena_isTerminal_iff source).mpr
            hsourceTerminal
        have htargetActions :
            IsEmpty
              ((macroExecutionKernelArena G D rootPayoff
                sourceDeclaredRoot).Action target) :=
          ((serializedBehavioralMacroPolicy_match G D rootPayoff
            sourceDeclaredRoot profile).terminal_iff hrelated).mp
              hsourceActions
        have htargetTerminal :
            (game G rootPayoff).isTerminal target.1 := by
          rw [hrelated]
          exact
            (boundary_isTerminal_iff G rootPayoff source).mpr
              hsourceTerminal
        rw [Arena.stochasticHistoryPMFFrom_of_terminal
          (serializedBehavioralHistoryPolicy G D rootPayoff
            sourceDeclaredRoot profile)
          target htargetTerminal]
        simp [KernelArena.stateLawFrom, htargetActions]
        rfl
      · have hsourceActions :
            ¬ IsEmpty (G.historyKernelArena.Action source) := by
          rw [G.historyKernelArena_isTerminal_iff]
          exact hsourceTerminal
        have htargetActions :
            ¬ IsEmpty
              ((macroExecutionKernelArena G D rootPayoff
                sourceDeclaredRoot).Action target) :=
          (not_congr
            ((serializedBehavioralMacroPolicy_match G D rootPayoff
              sourceDeclaredRoot profile).terminal_iff hrelated)).mp
                hsourceActions
        have hfuel :
            (Nat.succ horizon) * (n + 2) =
              (n + 2) + horizon * (n + 2) := by
          rw [Nat.succ_mul, Nat.add_comm]
        rw [hfuel]
        rw [Arena.stochasticHistoryPMFFrom_add]
        rw [serializedBehavioralExecution_eq_macroStepLaw
          G D rootPayoff sourceDeclaredRoot profile source
          hsourceTerminal target hrelated htargetActions]
        simp only [KernelArena.stateLawFrom, dif_neg htargetActions]
        apply PMF.bind_congr_support
        intro nextTarget hnextTarget
        have hstepCoupling :=
          (serializedBehavioralMacroPolicy_match G D rootPayoff
            sourceDeclaredRoot profile).stepCoupling
              hrelated hsourceActions htargetActions
        obtain ⟨nextSource, _, hnextRelated⟩ :=
          hstepCoupling.exists_left_of_mem_support_right
            hnextTarget
        exact ih hnextRelated

/-- Under coupling-compatible randomized policies, the source FOSG and its
serialized EFG have an exact coupling of every finite macro trace.

Both marginals are the actual trace PMFs.  Every positive-mass pair is related
at each macro boundary by `Rel G`. -/
theorem macroTraceLawCoupling
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (sourcePolicy : G.historyKernelArena.Policy)
    (targetPolicy :
      (macroExecutionKernelArena G D rootPayoff
        sourceDeclaredRoot).Policy)
    (matchPolicy :
      (macroKernelSimulation G D rootPayoff sourceDeclaredRoot).PolicyMatch
        sourcePolicy targetPolicy)
    {source : G.HistoryState}
    {target :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init}
    (hrelated : Rel G source target)
    (horizon : Nat) :
    PMF.RelCoupling (List.Forall₂ (Rel G))
      (G.historyKernelArena.traceLawFrom
        sourcePolicy horizon source)
      ((macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).traceLawFrom
        targetPolicy horizon target) := by
  exact matchPolicy.traceLawCoupling hrelated horizon

/-- The concrete policy compiler gives exact finite-horizon endpoint coupling
without requiring a caller-supplied target policy or matching witness. -/
theorem serializedMacroStateLawCoupling
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
    (horizon : Nat) :
    PMF.RelCoupling (Rel G)
      (G.historyKernelArena.stateLawFrom
        sourcePolicy horizon source)
      ((macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).stateLawFrom
        (serializedMacroPolicy G D rootPayoff sourceDeclaredRoot
          sourcePolicy)
        horizon target) :=
  (serializedMacroPolicy_match G D rootPayoff sourceDeclaredRoot
    sourcePolicy).stateLawCoupling hrelated horizon

/-- The concrete policy compiler gives exact complete-trace coupling without
requiring a caller-supplied target policy or matching witness. -/
theorem serializedMacroTraceLawCoupling
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
    (horizon : Nat) :
    PMF.RelCoupling (List.Forall₂ (Rel G))
      (G.historyKernelArena.traceLawFrom
        sourcePolicy horizon source)
      ((macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).traceLawFrom
        (serializedMacroPolicy G D rootPayoff sourceDeclaredRoot
          sourcePolicy)
        horizon target) :=
  macroTraceLawCoupling G D rootPayoff sourceDeclaredRoot
    sourcePolicy
    (serializedMacroPolicy G D rootPayoff sourceDeclaredRoot
      sourcePolicy)
    (serializedMacroPolicy_match G D rootPayoff sourceDeclaredRoot
      sourcePolicy)
    hrelated horizon

/-- Information-indexed behavioral profiles have exactly coupled stopped
finite traces after serialization. -/
theorem serializedBehavioralTraceLawCoupling
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (D : G.DecisionModel)
    (rootPayoff : Fin (n + 1) → U)
    (sourceDeclaredRoot : G.HistoryState → Prop)
    (profile : D.BehavioralProfile)
    {source : G.HistoryState}
    {target :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init}
    (hrelated : Rel G source target)
    (horizon : Nat) :
    PMF.RelCoupling (List.Forall₂ (Rel G))
      (G.historyKernelArena.traceLawFrom
        (D.behavioralHistoryPolicy profile) horizon source)
      ((macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).traceLawFrom
        (serializedBehavioralMacroPolicy G D rootPayoff
          sourceDeclaredRoot profile)
        horizon target) :=
  serializedMacroTraceLawCoupling G D rootPayoff sourceDeclaredRoot
    (D.behavioralHistoryPolicy profile) hrelated horizon

/-- The concrete serializer's payoff field agrees with the FOSG payoff vector
at every related macro boundary.

For nonterminal states this is an operational field equality; at terminal
states it is the economically meaningful terminal-payoff equality. -/
theorem payoff_eq_of_rel
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U)
    (source : G.HistoryState)
    (target :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init)
    (hrelated : Rel G source target) :
    (game G rootPayoff).payoff target.1 =
      G.payoff source.1 := by
  rw [hrelated]
  by_cases hterminal : G.isTerminal source.1
  · rw [boundary_of_terminal G source hterminal]
    rfl
  · rw [boundary_of_not_terminal G source hterminal]
    rfl

/-- Terminal payoff represented at a complete serialized history.

Nonterminal histories map to `none`; in particular, administrative states and
fuel-exhausted macro boundaries do not expose their operational payoff field.
-/
noncomputable def serializedStoppedPayoffAtHistory
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U)
    (history :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init) :
    Option (Fin (n + 1) → U) :=
  if (game G rootPayoff).isTerminal history.1 then
    some ((game G rootPayoff).payoff history.1)
  else
    none

/-- Related macro boundaries have exactly the same optional terminal payoff.
-/
theorem stoppedPayoff_eq_of_rel
    [(world : G.WorldState) → Decidable (G.isTerminal world)]
    (rootPayoff : Fin (n + 1) → U)
    (source : G.HistoryState)
    (target :
      (game G rootPayoff).toArena.HistoryFrom
        (game G rootPayoff).init)
    (hrelated : Rel G source target) :
    serializedStoppedPayoffAtHistory G rootPayoff target =
      G.stoppedPayoffAtHistory source := by
  have hterminal :
      (game G rootPayoff).isTerminal target.1 ↔
        G.isTerminal source.1 := by
    rw [hrelated]
    exact boundary_isTerminal_iff G rootPayoff source
  unfold serializedStoppedPayoffAtHistory
    FOSG.stoppedPayoffAtHistory
  by_cases hsourceTerminal : G.isTerminal source.1
  · have htargetTerminal :=
      hterminal.mpr hsourceTerminal
    simp [hsourceTerminal, htargetTerminal,
      payoff_eq_of_rel G rootPayoff source target hrelated]
  · have htargetNonterminal :
        ¬ (game G rootPayoff).isTerminal target.1 :=
      fun htargetTerminal =>
        hsourceTerminal (hterminal.mp htargetTerminal)
    simp [hsourceTerminal, htargetNonterminal]

/-- Exact equality of finite-horizon optional terminal-payoff laws under the
concrete policy compiler. -/
theorem serializedMacroPayoffLaw_eq
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
    (horizon : Nat) :
    (G.historyKernelArena.stateLawFrom
        sourcePolicy horizon source).map
          G.stoppedPayoffAtHistory =
      ((macroExecutionKernelArena G D rootPayoff
          sourceDeclaredRoot).stateLawFrom
        (serializedMacroPolicy G D rootPayoff sourceDeclaredRoot
          sourcePolicy)
        horizon target).map
          (serializedStoppedPayoffAtHistory G rootPayoff) := by
  exact
    (serializedMacroStateLawCoupling G D rootPayoff
      sourceDeclaredRoot sourcePolicy hrelated horizon).map_eq
        (fun sourceState targetHistory hrel =>
          (stoppedPayoff_eq_of_rel G rootPayoff sourceState
            targetHistory hrel).symm)


end ExtensiveGame.FOSG.Sequentialization
