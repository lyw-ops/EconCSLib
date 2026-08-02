/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Behavior
import EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Operational
import EconCSLib.GameTheory.GameForm.Basic

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.BehaviorMorphism

Behavioral-strategy and finite stochastic-outcome transfer along strict
observed chance-EFG isomorphisms.

The strict structural isomorphism transports information-indexed behavioral
strategies by exact `PMF` pushforward.  Its local information-action coherence
and chance-kernel coherence then imply that the induced stochastic history
policies commute at every corresponding history.  Consequently, every bounded
continuation history law and optional-terminal-payoff law is identical after
relabeling.

Because presentation-designated roots are part of the strict structure, these
continuation laws induce two-way transfer of finite-horizon behavioral Nash
equilibrium and the corresponding bounded Nash predicate on designated
continuations. Bounded behavioral subgame perfection on an explicit lawful
system uses the `...On` predicate below; complete standard behavioral SPE uses
a `CompleteSubgameSystem`.

## Main definitions

* `ObservedGame.Iso.behavioralStrategyEquiv` and
  `behavioralProfileEquiv` — exact transport of behavioral plans.
* `ObservedChanceGame.behavioralContinuationGameForm` — the bounded
  continuation game form whose outcome is an optional-terminal-payoff PMF.
* `ObservedChanceGame.IsBehavioralNashOnRootsAtFuel` —
  behavioral Nash at every presentation-designated continuation root under
  bounded stochastic execution.

## Main results

* `ObservedChanceGame.Iso.map_behavioralHistoryPolicy` — local policy
  naturality.
* `ObservedChanceGame.Iso.map_behavioralHistoryPMFFrom` and
  `map_behavioralStoppedPayoffLawFrom` — exact bounded stochastic semantics.
* `ObservedChanceGame.Iso.behavioralContinuationGameFormIso` — continuation
  game-form isomorphism.
* `ObservedChanceGame.Iso.isBehavioralNashOnRootsAtFuel_iff`
  — canonical public entry point for two-way bounded Nash transfer on
  presentation-designated continuations.
-/

namespace PMF

universe u v

variable {α : Type u} {β₁ β₂ : Type v}

/-- Casting the codomain of a pushed-forward PMF is the same as pushing
forward through the pointwise cast. -/
theorem cast_map
    (probability : PMF α)
    (function : α → β₁)
    (htype : β₁ = β₂) :
    cast (congrArg PMF htype) (probability.map function) =
      probability.map fun value => cast htype (function value) := by
  subst β₂
  rfl

end PMF

namespace ExtensiveGame.ObservedGame.Iso

variable {N U : Type*}
variable {G H : ObservedGame N U}

/-- Behavioral strategies transport by pushing every local action law through
the corresponding information-action equivalence. -/
noncomputable def behavioralStrategyEquiv (e : G.Iso H) (i : N) :
    G.BehavioralStrategy i ≃ H.BehavioralStrategy i :=
  (e.infoStateEquiv i).piCongr fun information =>
    PMF.mapEquiv (e.infoActionEquiv i information)

@[simp]
theorem behavioralStrategyEquiv_apply (e : G.Iso H) (i : N)
    (strategy : G.BehavioralStrategy i)
    (information : G.InfoState i) :
    e.behavioralStrategyEquiv i strategy
        (e.infoStateEquiv i information) =
      (strategy information).map
        (e.infoActionEquiv i information) := by
  simp [behavioralStrategyEquiv]

/-- Map a complete behavioral profile along a strict observed-EFG
isomorphism. -/
noncomputable def mapBehavioralProfile (e : G.Iso H)
    (profile : G.BehavioralProfile) :
    H.BehavioralProfile :=
  fun i => e.behavioralStrategyEquiv i (profile i)

/-- Map a target behavioral profile back through a strict observed-EFG
isomorphism. -/
noncomputable def unmapBehavioralProfile (e : G.Iso H)
    (profile : H.BehavioralProfile) :
    G.BehavioralProfile :=
  fun i => (e.behavioralStrategyEquiv i).symm (profile i)

/-- Strict observed-EFG isomorphisms induce an equivalence of complete
behavioral profiles. -/
noncomputable def behavioralProfileEquiv (e : G.Iso H) :
    G.BehavioralProfile ≃ H.BehavioralProfile where
  toFun := e.mapBehavioralProfile
  invFun := e.unmapBehavioralProfile
  left_inv := by
    intro profile
    funext i
    exact (e.behavioralStrategyEquiv i).symm_apply_apply (profile i)
  right_inv := by
    intro profile
    funext i
    exact (e.behavioralStrategyEquiv i).apply_symm_apply (profile i)

@[simp]
theorem mapBehavioralProfile_apply (e : G.Iso H)
    (profile : G.BehavioralProfile) (i : N) :
    e.mapBehavioralProfile profile i =
      e.behavioralStrategyEquiv i (profile i) :=
  rfl

@[simp]
theorem unmapBehavioralProfile_apply (e : G.Iso H)
    (profile : H.BehavioralProfile) (i : N) :
    e.unmapBehavioralProfile profile i =
      (e.behavioralStrategyEquiv i).symm (profile i) :=
  rfl

@[simp]
theorem mapBehavioralProfile_unmapBehavioralProfile (e : G.Iso H)
    (profile : H.BehavioralProfile) :
    e.mapBehavioralProfile (e.unmapBehavioralProfile profile) = profile :=
  (e.behavioralProfileEquiv).apply_symm_apply profile

@[simp]
theorem unmapBehavioralProfile_mapBehavioralProfile (e : G.Iso H)
    (profile : G.BehavioralProfile) :
    e.unmapBehavioralProfile (e.mapBehavioralProfile profile) = profile :=
  (e.behavioralProfileEquiv).symm_apply_apply profile

/-- Identity isomorphisms leave behavioral profiles unchanged. -/
@[simp]
theorem refl_mapBehavioralProfile
    (profile : G.BehavioralProfile) :
    (ObservedGame.Iso.refl G).mapBehavioralProfile profile =
      profile := by
  funext i information
  change
    (ObservedGame.Iso.refl G).behavioralStrategyEquiv i
        (profile i) information =
      profile i information
  rw [show
    (ObservedGame.Iso.refl G).behavioralStrategyEquiv i
        (profile i) information =
      (profile i information).map
        ((ObservedGame.Iso.refl G).infoActionEquiv
          i information) by
      exact
        behavioralStrategyEquiv_apply
          (ObservedGame.Iso.refl G) i
          (profile i) information]
  simpa using PMF.map_id (profile i information)

/-- Mapping behavioral profiles is functorial under composition of strict
observed-game isomorphisms. -/
@[simp]
theorem trans_mapBehavioralProfile {K : ObservedGame N U}
    (e : G.Iso H) (f : H.Iso K)
    (profile : G.BehavioralProfile) :
    (e.trans f).mapBehavioralProfile profile =
      f.mapBehavioralProfile (e.mapBehavioralProfile profile) := by
  funext i targetInformation
  obtain ⟨middleInformation, rfl⟩ :=
    (f.infoStateEquiv i).surjective targetInformation
  obtain ⟨sourceInformation, rfl⟩ :=
    (e.infoStateEquiv i).surjective middleInformation
  change
    (e.trans f).behavioralStrategyEquiv i
        (profile i)
        (f.infoStateEquiv i
          (e.infoStateEquiv i sourceInformation)) =
      f.behavioralStrategyEquiv i
        (e.behavioralStrategyEquiv i (profile i))
        (f.infoStateEquiv i
          (e.infoStateEquiv i sourceInformation))
  rw [show
    (e.trans f).behavioralStrategyEquiv i
        (profile i)
        (f.infoStateEquiv i
          (e.infoStateEquiv i sourceInformation)) =
      (profile i sourceInformation).map
        ((e.trans f).infoActionEquiv
          i sourceInformation) by
      exact
        behavioralStrategyEquiv_apply
          (e.trans f) i (profile i) sourceInformation]
  rw [behavioralStrategyEquiv_apply,
    behavioralStrategyEquiv_apply,
    PMF.map_comp]
  rfl

/-- A mapped behavioral profile's abstract action law at a corresponding
player history is the source law pushed through `infoActionEquivAt`. -/
theorem mapBehavioralProfile_infoAt
    (e : G.Iso H)
    (profile : G.BehavioralProfile)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hsource : G.base.mover history.1 = some i)
    (htarget :
      H.base.mover (e.historyIso.stateEquiv history).1 = some i) :
    e.mapBehavioralProfile profile i
        (H.infoAt (e.historyIso.stateEquiv history) i htarget) =
      (profile i (G.infoAt history i hsource)).map
        (e.infoActionEquivAt history i hsource htarget) := by
  let sourceInformation := G.infoAt history i hsource
  have hinfo :
      e.infoStateEquiv i sourceInformation =
        H.infoAt (e.historyIso.stateEquiv history) i htarget :=
    e.map_infoAt history i hsource htarget
  calc
    e.mapBehavioralProfile profile i
        (H.infoAt (e.historyIso.stateEquiv history) i htarget) =
      cast
        (congrArg
          (fun information => PMF (H.InfoAction i information))
          hinfo)
        (PMF.mapEquiv
          (e.infoActionEquiv i sourceInformation)
          (profile i sourceInformation)) := by
            exact
              Equiv.piCongr_apply_of_eq
                (W := fun information =>
                  PMF (G.InfoAction i information))
                (Z := fun information =>
                  PMF (H.InfoAction i information))
                (e.infoStateEquiv i)
                (fun information =>
                  PMF.mapEquiv
                    (e.infoActionEquiv i information))
                (profile i) sourceInformation
                (H.infoAt
                  (e.historyIso.stateEquiv history) i htarget)
                hinfo
    _ = (profile i sourceInformation).map
        (e.infoActionEquivAt history i hsource htarget) := by
          change
            cast
                (congrArg
                  (fun information =>
                    PMF (H.InfoAction i information))
                  hinfo)
                ((profile i sourceInformation).map
                  (e.infoActionEquiv i sourceInformation)) =
              (profile i sourceInformation).map
                (e.infoActionEquivAt
                  history i hsource htarget)
          rw [PMF.cast_map]
          rfl

/-- At corresponding player histories, the concrete behavioral action law is
the exact pushforward of the source law through the strict history-action
equivalence. -/
theorem map_behavioralActionLaw
    (e : G.Iso H)
    (profile : G.BehavioralProfile)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (i : N)
    (hsource : G.base.mover history.1 = some i)
    (htarget :
      H.base.mover (e.historyIso.stateEquiv history).1 = some i) :
    (profile.actionLawAt G history i hsource).map
        (e.historyIso.actionEquiv history) =
      (e.mapBehavioralProfile profile).actionLawAt H
        (e.historyIso.stateEquiv history) i htarget := by
  unfold ObservedGame.BehavioralProfile.actionLawAt
    ObservedGame.BehavioralStrategy.actionLawAt
  rw [mapBehavioralProfile_infoAt e profile history i hsource htarget]
  let probability :=
    profile i (G.infoAt history i hsource)
  calc
    (probability.map (G.actionEquiv history i hsource)).map
        (e.historyIso.actionEquiv history) =
      probability.map
        ((e.historyIso.actionEquiv history) ∘
          (G.actionEquiv history i hsource)) :=
      PMF.map_comp
        (G.actionEquiv history i hsource)
        probability
        (e.historyIso.actionEquiv history)
    _ = probability.map
        ((H.actionEquiv
            (e.historyIso.stateEquiv history) i htarget) ∘
          (e.infoActionEquivAt history i hsource htarget)) := by
          apply congrArg (fun actionMap => probability.map actionMap)
          funext action
          exact
            (e.map_infoActionEquivAt
              history i hsource htarget action).symm
    _ = (probability.map
          (e.infoActionEquivAt history i hsource htarget)).map
        (H.actionEquiv
          (e.historyIso.stateEquiv history) i htarget) :=
      (PMF.map_comp
        (e.infoActionEquivAt history i hsource htarget)
        probability
        (H.actionEquiv
          (e.historyIso.stateEquiv history) i htarget)).symm

end ExtensiveGame.ObservedGame.Iso

namespace ExtensiveGame.ObservedChanceGame.Iso

variable {N U : Type*}
variable {G H : ObservedChanceGame N U}

/-- The stochastic history policies induced by corresponding behavioral
profiles commute exactly with the strict history-action equivalences. -/
theorem map_behavioralHistoryPolicy
    (e : G.Iso H)
    (profile : G.observed.BehavioralProfile)
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (hsource :
      ¬ G.observed.base.isTerminal history.1)
    (htarget :
      ¬ H.observed.base.isTerminal
        (e.observedIso.historyIso.stateEquiv history).1) :
    ((BehavioralProfile.toHistoryPolicy G profile)
        history hsource).map
          (e.observedIso.historyIso.actionEquiv history) =
      (BehavioralProfile.toHistoryPolicy H
        (e.observedIso.mapBehavioralProfile profile))
        (e.observedIso.historyIso.stateEquiv history)
        htarget := by
  cases hmover : G.observed.base.mover history.1 with
  | some i =>
      have htargetMover :
          H.observed.base.mover
              (e.observedIso.historyIso.stateEquiv history).1 =
            some i := by
        rw [e.observedIso.map_mover history]
        exact hmover
      rw [BehavioralProfile.toHistoryPolicy_of_mover
        G profile history hsource i hmover]
      rw [BehavioralProfile.toHistoryPolicy_of_mover
        H (e.observedIso.mapBehavioralProfile profile)
        (e.observedIso.historyIso.stateEquiv history)
        htarget i htargetMover]
      exact
        e.observedIso.map_behavioralActionLaw
          profile history i hmover htargetMover
  | none =>
      have hsourceChance :
          G.observed.base.isChanceState history.1 :=
        ⟨hmover, hsource⟩
      have htargetMover :
          H.observed.base.mover
              (e.observedIso.historyIso.stateEquiv history).1 =
            none := by
        rw [e.observedIso.map_mover history]
        exact hmover
      rw [BehavioralProfile.toHistoryPolicy_of_chance
        G profile history hsource hmover]
      rw [BehavioralProfile.toHistoryPolicy_of_chance
        H (e.observedIso.mapBehavioralProfile profile)
        (e.observedIso.historyIso.stateEquiv history)
        htarget htargetMover]
      exact e.map_chanceKernel history hsourceChance

/-- Exact naturality of bounded stochastic continuation execution under a
strict observed chance-EFG isomorphism. -/
theorem map_behavioralHistoryPMFFrom
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable (H.observed.base.isTerminal state)]
    (e : G.Iso H)
    (profile : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init) :
    ∀ fuel,
      (G.observed.base.toArena.stochasticHistoryPMFFrom
          (BehavioralProfile.toHistoryPolicy G profile)
          current fuel).map
          e.observedIso.historyIso.stateEquiv =
        H.observed.base.toArena.stochasticHistoryPMFFrom
          (BehavioralProfile.toHistoryPolicy H
            (e.observedIso.mapBehavioralProfile profile))
          (e.observedIso.historyIso.stateEquiv current)
          fuel := by
  intro fuel
  induction fuel generalizing current with
  | zero =>
      exact
        PMF.pure_map
          e.observedIso.historyIso.stateEquiv current
  | succ fuel ih =>
      by_cases hsource :
          G.observed.base.isTerminal current.1
      · have htarget :
            H.observed.base.isTerminal
              (e.observedIso.historyIso.stateEquiv current).1 :=
          (e.observedIso.isTerminal_iff current).mp hsource
        rw [Arena.stochasticHistoryPMFFrom_succ_of_terminal
          (BehavioralProfile.toHistoryPolicy G profile)
          current fuel hsource]
        rw [Arena.stochasticHistoryPMFFrom_succ_of_terminal
          (BehavioralProfile.toHistoryPolicy H
            (e.observedIso.mapBehavioralProfile profile))
          (e.observedIso.historyIso.stateEquiv current)
          fuel htarget]
        exact
          PMF.pure_map
            e.observedIso.historyIso.stateEquiv current
      · have htarget :
            ¬ H.observed.base.isTerminal
              (e.observedIso.historyIso.stateEquiv current).1 :=
          not_congr
            (e.observedIso.isTerminal_iff current) |>.mp hsource
        rw [Arena.stochasticHistoryPMFFrom_succ_of_not_terminal
          (BehavioralProfile.toHistoryPolicy G profile)
          current fuel hsource]
        rw [Arena.stochasticHistoryPMFFrom_succ_of_not_terminal
          (BehavioralProfile.toHistoryPolicy H
            (e.observedIso.mapBehavioralProfile profile))
          (e.observedIso.historyIso.stateEquiv current)
          fuel htarget]
        let sourcePolicy :=
          BehavioralProfile.toHistoryPolicy G profile
        let targetPolicy :=
          BehavioralProfile.toHistoryPolicy H
            (e.observedIso.mapBehavioralProfile profile)
        let sourceLaw := sourcePolicy current hsource
        let targetContinuation :=
          fun action =>
            H.observed.base.toArena.stochasticHistoryPMFFrom
              targetPolicy
              ⟨H.observed.base.next
                  (e.observedIso.historyIso.stateEquiv current).1
                  action,
                (e.observedIso.historyIso.stateEquiv current).2.snoc
                  action⟩
              fuel
        calc
          (sourceLaw.bind
              (fun action =>
                G.observed.base.toArena.stochasticHistoryPMFFrom
                  sourcePolicy
                  ⟨G.observed.base.next current.1 action,
                    current.2.snoc action⟩
                  fuel)).map
                e.observedIso.historyIso.stateEquiv =
            sourceLaw.bind
              (fun action =>
                (G.observed.base.toArena.stochasticHistoryPMFFrom
                    sourcePolicy
                    ⟨G.observed.base.next current.1 action,
                      current.2.snoc action⟩
                    fuel).map
                  e.observedIso.historyIso.stateEquiv) :=
                    PMF.map_bind sourceLaw
                      (fun action =>
                        G.observed.base.toArena.stochasticHistoryPMFFrom
                          sourcePolicy
                          ⟨G.observed.base.next current.1 action,
                            current.2.snoc action⟩
                          fuel)
                      e.observedIso.historyIso.stateEquiv
          _ =
            sourceLaw.bind
              (fun action =>
                H.observed.base.toArena.stochasticHistoryPMFFrom
                  targetPolicy
                  (e.observedIso.historyIso.stateEquiv
                    ⟨G.observed.base.next current.1 action,
                      current.2.snoc action⟩)
                  fuel) := by
                    apply congrArg
                      (fun continuation =>
                        sourceLaw.bind continuation)
                    funext action
                    exact ih
                      ⟨G.observed.base.next current.1 action,
                        current.2.snoc action⟩
          _ = sourceLaw.bind
              (targetContinuation ∘
                e.observedIso.historyIso.actionEquiv current) := by
                  apply congrArg
                    (fun continuation =>
                      sourceLaw.bind continuation)
                  funext action
                  unfold targetContinuation
                  change
                    H.observed.base.toArena.stochasticHistoryPMFFrom
                        targetPolicy
                        (e.observedIso.historyIso.stateEquiv
                          ⟨G.observed.base.next current.1 action,
                            current.2.snoc action⟩)
                        fuel =
                      H.observed.base.toArena.stochasticHistoryPMFFrom
                        targetPolicy
                        ⟨H.observed.base.next
                            (e.observedIso.historyIso.stateEquiv
                              current).1
                            (e.observedIso.historyIso.actionEquiv
                              current action),
                          (e.observedIso.historyIso.stateEquiv
                            current).2.snoc
                            (e.observedIso.historyIso.actionEquiv
                              current action)⟩
                        fuel
                  apply congrArg
                    (fun next =>
                      H.observed.base.toArena.stochasticHistoryPMFFrom
                        targetPolicy next fuel)
                  exact
                    e.observedIso.historyIso.map_next current action
          _ = (sourceLaw.map
                (e.observedIso.historyIso.actionEquiv current)).bind
              targetContinuation :=
                (PMF.bind_map sourceLaw
                  (e.observedIso.historyIso.actionEquiv current)
                  targetContinuation).symm
          _ = (targetPolicy
                (e.observedIso.historyIso.stateEquiv current)
                htarget).bind targetContinuation := by
                  rw [e.map_behavioralHistoryPolicy
                    profile current hsource htarget]
                  rfl

end ExtensiveGame.ObservedChanceGame.Iso

namespace ExtensiveGame.ObservedChanceGame

universe uV

variable {N U : Type*}

/-- Terminal payoff represented at a complete history.  Nonterminal histories
map to `none`, so bounded execution never treats a fuel-exhausted prefix as a
terminal outcome. -/
def stoppedPayoffAtHistory (G : ObservedChanceGame N U)
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init) :
    Option (N → U) :=
  if G.observed.base.isTerminal history.1 then
    some (G.observed.base.payoff history.1)
  else
    none

/-- The bounded law of an optional terminal payoff from an accumulated
history under a behavioral profile.  Nonterminal exhaustion is represented
by `none`. -/
noncomputable def behavioralStoppedPayoffLawFrom
    (G : ObservedChanceGame N U)
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (profile : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (fuel : ℕ) :
    PMF (Option (N → U)) :=
  (G.observed.base.toArena.stochasticHistoryPMFFrom
      (BehavioralProfile.toHistoryPolicy G profile)
      current fuel).map
    G.stoppedPayoffAtHistory

/-- The bounded behavioral continuation game form at an accumulated history.

Its outcome retains the entire probability law on optional terminal payoff
vectors.  Expected utility, risk-sensitive utility, or any other preference
functional on that law can therefore be supplied externally. -/
noncomputable def behavioralContinuationGameForm
    (G : ObservedChanceGame N U)
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (fuel : ℕ) :
    GameForm N where
  Strategy := G.observed.BehavioralStrategy
  Outcome := PMF (Option (N → U))
  outcome profile :=
    G.behavioralStoppedPayoffLawFrom profile current fuel

/-- Bounded behavioral Nash equilibrium on presentation-designated
continuations.

The same complete contingent behavioral profile must be Nash in the stochastic
continuation game at every designated root. The predicate makes no claim that
the root predicate is a lawful standard-subgame system. The caller controls how a
probability law with possible fuel-exhaustion mass (`none`) is evaluated. -/
def IsBehavioralNashOnRootsAtFuel
    (G : ObservedChanceGame N U)
    [DecidableEq N] [Preorder V]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (roots : G.observed.RootPresentation)
    (utility : PMF (Option (N → U)) → N → V)
    (profile : G.observed.BehavioralProfile)
    (fuel : ℕ) : Prop :=
  ∀ current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init,
    roots.IsRoot current →
      (G.behavioralContinuationGameForm current fuel).IsNash
        utility profile

/-- Bounded behavioral subgame perfection on an explicit, possibly
conservative, lawful subgame system of the observed game. -/
def IsBehavioralSubgamePerfectOnAtFuel
    (G : ObservedChanceGame N U)
    [DecidableEq N] [Preorder V]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (system : G.observed.SubgameSystem)
    (utility : PMF (Option (N → U)) → N → V)
    (profile : G.observed.BehavioralProfile)
    (fuel : ℕ) : Prop :=
  ∀ current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init,
    system.IsRoot current →
      (G.behavioralContinuationGameForm current fuel).IsNash
        utility profile

/-- Bounded standard behavioral SPE on every structurally lawful subgame
root. -/
def IsBehavioralStandardSubgamePerfectAtFuel
    (G : ObservedChanceGame N U)
    [DecidableEq N] [Preorder V]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (system : G.observed.CompleteSubgameSystem)
    (utility : PMF (Option (N → U)) → N → V)
    (profile : G.observed.BehavioralProfile)
    (fuel : ℕ) : Prop :=
  G.IsBehavioralSubgamePerfectOnAtFuel system.toSubgameSystem
    utility profile fuel

namespace Iso

variable {G H : ObservedChanceGame N U}

/-- The optional terminal payoff represented at corresponding histories is
identical. -/
theorem map_stoppedPayoffAtHistory
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable (H.observed.base.isTerminal state)]
    (e : G.Iso H)
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init) :
    H.stoppedPayoffAtHistory
        (e.observedIso.historyIso.stateEquiv history) =
      G.stoppedPayoffAtHistory history := by
  unfold stoppedPayoffAtHistory
  by_cases hsource :
      G.observed.base.isTerminal history.1
  · have htarget :
        H.observed.base.isTerminal
          (e.observedIso.historyIso.stateEquiv history).1 :=
      (e.observedIso.isTerminal_iff history).mp hsource
    rw [if_pos hsource, if_pos htarget,
      e.observedIso.map_payoff history hsource]
  · have htarget :
        ¬ H.observed.base.isTerminal
          (e.observedIso.historyIso.stateEquiv history).1 :=
      not_congr
        (e.observedIso.isTerminal_iff history) |>.mp hsource
    rw [if_neg hsource, if_neg htarget]

/-- Strict observed chance-EFG isomorphisms preserve the entire bounded
optional-terminal-payoff law at every continuation. -/
theorem map_behavioralStoppedPayoffLawFrom
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable (H.observed.base.isTerminal state)]
    (e : G.Iso H)
    (profile : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (fuel : ℕ) :
    H.behavioralStoppedPayoffLawFrom
        (e.observedIso.mapBehavioralProfile profile)
        (e.observedIso.historyIso.stateEquiv current)
        fuel =
      G.behavioralStoppedPayoffLawFrom profile current fuel := by
  unfold behavioralStoppedPayoffLawFrom
  rw [← e.map_behavioralHistoryPMFFrom profile current fuel]
  let sourceLaw :=
    G.observed.base.toArena.stochasticHistoryPMFFrom
      (BehavioralProfile.toHistoryPolicy G profile)
      current fuel
  calc
    (sourceLaw.map
        e.observedIso.historyIso.stateEquiv).map
          H.stoppedPayoffAtHistory =
      sourceLaw.map
        (H.stoppedPayoffAtHistory ∘
          e.observedIso.historyIso.stateEquiv) :=
            PMF.map_comp
              e.observedIso.historyIso.stateEquiv
              sourceLaw
              H.stoppedPayoffAtHistory
    _ = sourceLaw.map G.stoppedPayoffAtHistory := by
          apply congrArg
            (fun outcomeMap => sourceLaw.map outcomeMap)
          funext history
          exact e.map_stoppedPayoffAtHistory history

/-- Corresponding bounded behavioral continuation games are strictly
isomorphic. -/
noncomputable def behavioralContinuationGameFormIso
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable (H.observed.base.isTerminal state)]
    (e : G.Iso H)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (fuel : ℕ) :
    (G.behavioralContinuationGameForm current fuel).Iso
      (H.behavioralContinuationGameForm
        (e.observedIso.historyIso.stateEquiv current) fuel) where
  strategyEquiv := e.observedIso.behavioralStrategyEquiv
  outcomeEquiv := Equiv.refl _
  map_outcome := by
    intro profile
    exact
      (e.map_behavioralStoppedPayoffLawFrom
        profile current fuel).symm

/-- The continuation game-form isomorphism is compatible with a common
functional on payoff laws. -/
theorem behavioralContinuationGameFormIso_utilityCompatible
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable (H.observed.base.isTerminal state)]
    (e : G.Iso H)
    (utility : PMF (Option (N → U)) → N → V)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (fuel : ℕ) :
    GameForm.Iso.UtilityCompatible
      (e.behavioralContinuationGameFormIso current fuel)
      utility utility := by
  intro outcome i
  rfl

/-- Behavioral Nash equilibrium transfers in both directions at every
corresponding bounded continuation. -/
theorem behavioralContinuationIsNash_iff
    [DecidableEq N] [Preorder V]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable (H.observed.base.isTerminal state)]
    (e : G.Iso H)
    (utility : PMF (Option (N → U)) → N → V)
    (profile : G.observed.BehavioralProfile)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (fuel : ℕ) :
    (G.behavioralContinuationGameForm current fuel).IsNash
        utility profile ↔
      (H.behavioralContinuationGameForm
        (e.observedIso.historyIso.stateEquiv current)
        fuel).IsNash
          utility
          (e.observedIso.mapBehavioralProfile profile) := by
  exact
    (e.behavioralContinuationGameFormIso current fuel).isNash_iff
      (e.behavioralContinuationGameFormIso_utilityCompatible
        utility current fuel)
      profile

/-- A strict observed chance-EFG isomorphism preserves bounded behavioral
Nash equilibrium on explicitly corresponding root presentations in both
directions. -/
theorem isBehavioralNashOnRootsAtFuel_iff
    [DecidableEq N] [Preorder V]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    [(state : H.observed.base.State) →
      Decidable (H.observed.base.isTerminal state)]
    (e : G.Iso H)
    (sourceRoots : G.observed.RootPresentation)
    (targetRoots : H.observed.RootPresentation)
    (hroots :
      e.observedIso.PreservesRootPresentations
        sourceRoots targetRoots)
    (utility : PMF (Option (N → U)) → N → V)
    (profile : G.observed.BehavioralProfile)
    (fuel : ℕ) :
    G.IsBehavioralNashOnRootsAtFuel sourceRoots utility profile fuel ↔
      H.IsBehavioralNashOnRootsAtFuel targetRoots utility
        (e.observedIso.mapBehavioralProfile profile) fuel := by
  constructor
  · intro hspe targetRoot htargetRoot
    let sourceRoot :=
      e.observedIso.historyIso.stateEquiv.symm targetRoot
    have hmap :
        e.observedIso.historyIso.stateEquiv sourceRoot =
          targetRoot :=
      e.observedIso.historyIso.stateEquiv.apply_symm_apply
        targetRoot
    have hsourceRoot : sourceRoots.IsRoot sourceRoot := by
      apply (hroots sourceRoot).mpr
      simpa [hmap] using htargetRoot
    have hsourceNash := hspe sourceRoot hsourceRoot
    have hmapped :=
      (e.behavioralContinuationIsNash_iff
        utility profile sourceRoot fuel).mp hsourceNash
    change
      (H.behavioralContinuationGameForm
        (e.observedIso.historyIso.stateEquiv sourceRoot)
        fuel).IsNash
          utility
          (e.observedIso.mapBehavioralProfile profile) at hmapped
    rw [hmap] at hmapped
    exact hmapped
  · intro hspe sourceRoot hsourceRoot
    have htargetRoot :
        targetRoots.IsRoot
          (e.observedIso.historyIso.stateEquiv sourceRoot) :=
      (hroots sourceRoot).mp hsourceRoot
    have htargetNash :=
      hspe
        (e.observedIso.historyIso.stateEquiv sourceRoot)
        htargetRoot
    exact
      (e.behavioralContinuationIsNash_iff
        utility profile sourceRoot fuel).mpr htargetNash

end Iso

end ExtensiveGame.ObservedChanceGame
