/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.KernelArena
import EconCSLib.GameTheory.ExtensiveGame.Observed.Chance

/-!
# EconCSLib.Examples.ExtensiveGame.CouplingBoundary

Finite probability guarding example **N-4** for the strict separation between
a relational coupling and a deterministic equivalence pushforward.

Both laws live on the finite two-point type `Bool`. The source has atomic
weights `{1/3, 2/3}`, while the target is fair with weights `{1/2, 1/2}`.
Their coarse observable forgets the Boolean label. The independent joint law
is an exact `PMF.RelCoupling`: both marginals are literally the declared PMFs,
and every supported pair preserves that observable.

`PMF.RelCoupling.map_eq` then gives exact equality of the coarse observable
laws. In contrast, `no_equivPushforward` quantifies over every
`Bool ≃ Bool`: an equivalence only permutes the source atom weights and cannot
produce the fair target. Thus coupling-level comparison is strictly weaker
than the pushforward equality required by a strict chance-game isomorphism.
The final theorem instantiates that boundary inside two otherwise identical
one-state observed chance games and excludes every strict chance-game
isomorphism between them. The example does not claim that every coupling rules
out such a pushforward.
-/

namespace Examples.CouplingBoundary

open ExtensiveGame

/-- The nonuniform source law, with true mass `1/3` and false mass `2/3`. -/
noncomputable def sourceLaw : PMF Bool :=
  PMF.bernoulli (1 / 3) (by
    apply div_le_one_of_le₀
    · norm_num
    · positivity)

/-- The fair target law. -/
noncomputable def targetLaw : PMF Bool :=
  PMF.bernoulli (1 / 2) (by norm_num)

/-- The selected coarse observable forgets the Boolean atom label. -/
def coarseObservable (_ : Bool) : Unit :=
  ()

/-- Cross-law states are related exactly when their coarse observations
agree. -/
def Related (source target : Bool) : Prop :=
  coarseObservable source = coarseObservable target

/-- Concrete joint PMF used as the coupling witness. -/
noncomputable def witnessCoupling :
    PMF (Bool × Bool) :=
  PMF.independentCoupling sourceLaw targetLaw

/-- Every supported pair of the concrete joint law satisfies the coarse
cross-type relation. -/
theorem witnessCoupling_supported :
    ∀ pair ∈ witnessCoupling.support,
      Related pair.1 pair.2 := by
  intro pair hpair
  rfl

/-- **N-4.** The two finite atomic laws admit a relational coupling with exact
marginals and relation-supported mass. -/
theorem coupling_exists :
    PMF.RelCoupling Related sourceLaw targetLaw := by
  exact
    ⟨witnessCoupling,
      PMF.independentCoupling_map_fst
        sourceLaw targetLaw,
      PMF.independentCoupling_map_snd
        sourceLaw targetLaw,
      witnessCoupling_supported⟩

/-- The support relation is not the graph of a deterministic map: the
particular source state `false` is related to both distinct target states. -/
theorem relation_not_rightUnique :
    ¬ ∀ sourceState leftState rightState,
        Related sourceState leftState →
          Related sourceState rightState →
            leftState = rightState := by
  intro h
  exact Bool.noConfusion
    (h false false true rfl rfl)

/-- The exact coupling does not identify the raw PMFs: their mass at `true`
is respectively `1/3` and `1/2`. -/
theorem sourceLaw_ne_targetLaw :
    sourceLaw ≠ targetLaw := by
  intro heq
  have hmass :=
    congrArg (fun law : PMF Bool => law true) heq
  simp [sourceLaw, targetLaw, PMF.bernoulli_apply] at hmass

/-- **N-4, universal separation.** No equivalence of the two-point atom type
pushes the nonuniform source law to the fair target law.

This rules out every deterministic relabeling, not merely the identity or one
chosen equivalence: evaluating a hypothetical equality at `e true` recovers
source mass `1/3`, while the fair target has mass `1/2` at either Boolean
atom. It is the negative counterpart to the exact coupling above. -/
theorem no_equivPushforward :
    ∀ e : Bool ≃ Bool,
      sourceLaw.map e ≠ targetLaw := by
  intro e heq
  have hmass :=
    congrArg
      (fun law : PMF Bool => law (e true))
      heq
  dsimp only at hmass
  have hsource :
      sourceLaw.map e (e true) =
        sourceLaw true := by
    calc
      sourceLaw.map e (e true) =
          sourceLaw (e.symm (e true)) :=
        PMF.map_equiv_apply sourceLaw e (e true)
      _ = sourceLaw true := by
        rw [e.symm_apply_apply]
  rw [hsource] at hmass
  cases hvalue : e true <;>
    simp [sourceLaw, targetLaw, PMF.bernoulli_apply,
      hvalue] at hmass

/-- Equality follows only after explicit observable maps are supplied and
shown equal on related support. This is the functional bridge
`PMF.RelCoupling.map_eq`, not definitional equality of the original PMFs. -/
theorem coarseObservableLaw_eq :
    sourceLaw.map coarseObservable =
      targetLaw.map coarseObservable :=
  coupling_exists.map_eq
    (fun _ _ hrelated => hrelated)

/-! ### Strict observed chance-game integration -/

/-- A one-state chance arena with a Boolean action at every history.

The arena deliberately has no player-controlled or terminal states: the
integration regression needs only the initial strict chance-kernel square. -/
def chanceBase : ExtensiveGame Unit Unit where
  State := Unit
  Action := fun _ => Bool
  next := fun _ _ => ()
  init := ()
  mover := fun _ => none
  payoff := fun _ _ => ()

/-- Trivial observations over the one-state chance arena. Player-information
fields are discharged by the fact that the arena has no player mover. -/
def chanceObserved : ObservedGame Unit Unit where
  base := chanceBase
  Observation := fun _ => Unit
  PublicObservation := Unit
  observe := fun _ _ => ()
  publicObserve := fun _ => ()
  publicOf := fun _ _ => ()
  observe_public := fun _ _ => rfl
  InfoState := fun _ => Unit
  infoObserve := fun _ _ => ()
  infoAt := by
    intro history i hmover
    simp [chanceBase] at hmover
  infoAt_observe := by
    intro history i hmover
    simp [chanceBase] at hmover
  InfoAction := fun _ _ => Bool
  actionEquiv := by
    intro history i hmover
    simp [chanceBase] at hmover

/-- The initial complete history of the one-state chance arena. -/
def chanceInitial :
    chanceObserved.base.toArena.HistoryFrom
      chanceObserved.base.init :=
  Arena.HistoryFrom.nil
    chanceObserved.base.toArena
    chanceObserved.base.init

/-- The initial state is a genuine chance state. -/
theorem chanceInitial_isChance :
    chanceObserved.base.isChanceState chanceInitial.1 := by
  constructor
  · rfl
  · intro hterminal
    exact hterminal.false false

/-- The observed chance game carrying the nonuniform source kernel. -/
noncomputable def sourceChanceGame :
    ObservedChanceGame Unit Unit where
  observed := chanceObserved
  chanceKernel := fun _ _ => sourceLaw

/-- The otherwise identical observed chance game carrying the fair target
kernel. -/
noncomputable def targetChanceGame :
    ObservedChanceGame Unit Unit where
  observed := chanceObserved
  chanceKernel := fun _ _ => targetLaw

/-- **N-4, strict chance-game integration.** No strict observed chance-game
isomorphism exists from the nonuniform-kernel game to the fair-kernel game.

At the initial history, every strict isomorphism would supply a Boolean action
equivalence whose pushforward sends `sourceLaw` to `targetLaw`, contradicting
`no_equivPushforward`. This exercises the exact `map_chanceKernel` field rather
than inferring a no-isomorphism result merely from the existence of a
coupling. -/
theorem no_strictChanceIso :
    ¬ Nonempty (sourceChanceGame.Iso targetChanceGame) := by
  rintro ⟨e⟩
  let actionRelabeling : Bool ≃ Bool :=
    e.observedIso.historyIso.actionEquiv chanceInitial
  have hkernel :=
    e.map_chanceKernel chanceInitial chanceInitial_isChance
  apply no_equivPushforward actionRelabeling
  simpa [sourceChanceGame, targetChanceGame,
    actionRelabeling] using hkernel

end Examples.CouplingBoundary
