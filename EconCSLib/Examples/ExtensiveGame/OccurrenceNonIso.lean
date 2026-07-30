/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Compiler.GameTreeOccurrenceObserved

/-!
# EconCSLib.Examples.ExtensiveGame.OccurrenceNonIso

Deterministic guarding example **N-1** from the living EFG correctness record
(`docs/research/efg_strict_correctness_audit.md`).

The endpoint-sensitive compiler `GameTree.toObservedGame` and the
occurrence-sensitive compiler `GameTree.toOccurrenceObservedGame` are connected
by the directional certificate `ObservedGame.InformationRefinement`. This
module exhibits why the canonical certificate is not a strict information
relabeling: a finite `GameTree` contains one player-controlled subtree value at
two genuinely distinct history occurrences.

The occurrence compiler keeps these two histories apart (its information state
is the full history), while the endpoint compiler collapses them to a single
`NodeInfo`.  The forgetting map `GameTree.forgetOccurrenceInfo` therefore
identifies two distinct occurrence information states, so it is not injective,
and hence cannot be the information-state equivalence of a strict isomorphism.
That noninjectivity theorem alone does not rule out every conceivable
isomorphism.  The separate theorem `not_nonempty_iso` does so in the stated
endpoint-to-occurrence direction by using `ObservedGame.Iso.map_infoAt` and
injectivity of its history equivalence.

## The game

```
        root            (player 1)
       /    \
  repeated  middle       (middle: player 1)
    / \        |
  leaf leaf  repeated     (repeated: player 0)
              / \
            leaf leaf
```

`repeated` is a player-0 node.  It occurs directly under `root` and again under
`middle`, at two distinct histories with the same endpoint subtree value.

## Main results

* `Examples.OccurrenceNonIso.firstOcc_ne_secondOcc` — the two occurrences are
  distinct occurrence information states.
* `Examples.OccurrenceNonIso.forgetOccurrenceInfo_merges` — they are identified
  by the endpoint forgetting map.
* `Examples.OccurrenceNonIso.forgetOccurrenceInfo_not_injective` — the endpoint
  information-forgetting map is not injective, instantiating
  `GameTree.not_injective_forgetOccurrenceInfo_of_merged_histories`.
* `Examples.OccurrenceNonIso.separatingOccurrenceStrategy_distinguishes` — an
  occurrence strategy makes different choices at the two occurrences.
* `Examples.OccurrenceNonIso.endpointLift_same_choice` — every lifted endpoint
  strategy makes the same choice at both occurrences.
* `Examples.OccurrenceNonIso.not_nonempty_iso` — every strict observed-game
  isomorphism in the endpoint-to-occurrence direction is ruled out by the
  merged histories, using a separate structural argument.
* `Examples.OccurrenceNonIso.endpointOccurrenceRefinement_exists` — the
  concrete compilers carry the intended directional refinement certificate.
-/

namespace Examples.OccurrenceNonIso

open GameTree

/-- Two players; player `0` owns the repeated decision subtree. -/
abbrev Player := Fin 2

/-- The (irrelevant) common leaf payoff. -/
def leafPayoff : Player → ℤ := fun _ => 0

/-- A distinct alternative leaf payoff, making the repeated choice
nontrivial. -/
def alternativePayoff : Player → ℤ := fun _ => 1

/-- A player-`0` decision subtree that appears at two occurrences. -/
def repeated : GameTree Player ℤ :=
  .Node 0 (.Leaf leafPayoff) [.Leaf alternativePayoff]

/-- A player-`1` detour whose only child is `repeated`. -/
def middle : GameTree Player ℤ := .Node 1 repeated []

/-- The root: player `1` may move directly into `repeated`, or first into
`middle` and then into `repeated`. -/
def root : GameTree Player ℤ := .Node 1 repeated [middle]

/-- The action selecting `repeated` directly from `root`. -/
def rootToRepeated : (toExtensiveGame root).Action root :=
  ⟨repeated, List.mem_cons_self⟩

/-- The action selecting `middle` from `root`. -/
def rootToMiddle : (toExtensiveGame root).Action root :=
  ⟨middle, List.mem_cons_of_mem repeated List.mem_cons_self⟩

/-- The action selecting `repeated` from `middle`. -/
def middleToRepeated : (toExtensiveGame root).Action middle :=
  ⟨repeated, List.mem_cons_self⟩

/-- The length-`1` history reaching `repeated` directly from `root`. -/
def directHistory : (toExtensiveGame root).toArena.History root repeated :=
  (Arena.History.nil).snoc rootToRepeated

/-- The length-`2` history reaching `repeated` through `middle`. -/
def viaMiddleHistory : (toExtensiveGame root).toArena.History root repeated :=
  ((Arena.History.nil).snoc rootToMiddle).snoc middleToRepeated

/-- The direct occurrence of player `0`'s decision at `repeated`. -/
def firstOcc : (toOccurrenceObservedGame root).InfoState (0 : Player) :=
  ⟨⟨repeated, directHistory⟩, rfl⟩

/-- The occurrence of player `0`'s decision at `repeated` reached via `middle`. -/
def secondOcc : (toOccurrenceObservedGame root).InfoState (0 : Player) :=
  ⟨⟨repeated, viaMiddleHistory⟩, rfl⟩

/-- The two occurrences are genuinely distinct occurrence information states:
their underlying histories differ in length. -/
theorem firstOcc_ne_secondOcc : firstOcc ≠ secondOcc := by
  intro heq
  have hlen : directHistory.length = viaMiddleHistory.length :=
    congrArg
      (fun hf : (toExtensiveGame root).toArena.HistoryFrom root => hf.2.length)
      (congrArg Subtype.val heq)
  have hbad : (1 : ℕ) = 2 := hlen
  omega

/-- Both occurrences share the same endpoint subtree value `repeated`, so the
endpoint compiler merges them into a single `NodeInfo`. -/
theorem forgetOccurrenceInfo_merges :
    forgetOccurrenceInfo root (0 : Player) firstOcc =
      forgetOccurrenceInfo root 0 secondOcc :=
  forgetOccurrenceInfo_eq_of_endpoint_eq root 0 firstOcc secondOcc rfl

/-- **N-1.** The canonical endpoint information-forgetting map is not
injective, so it cannot serve as the information-state equivalence of a strict
isomorphism. This protects the directional refinement certificate from being
mistaken for a strict relabeling. -/
theorem forgetOccurrenceInfo_not_injective :
    ¬ Function.Injective (forgetOccurrenceInfo root (0 : Player)) :=
  not_injective_forgetOccurrenceInfo_of_merged_histories
    root 0 firstOcc secondOcc firstOcc_ne_secondOcc rfl

/-! ### Concrete strategy-space separation -/

/-- The first legal child at any player-`0` occurrence information state in
this example. -/
def firstLegalAction
    (information :
      (toOccurrenceObservedGame root).InfoState
        (0 : Player)) :
    (toOccurrenceObservedGame root).InfoAction 0 information := by
  rcases information with
    ⟨⟨endpoint, history⟩, hmover⟩
  cases endpoint with
  | Leaf payoff =>
      simp [toExtensiveGame] at hmover
  | Node mover head tail =>
      exact ⟨head, List.mem_cons_self⟩

/-- The alternative concrete action at the second occurrence. -/
def secondAlternativeAction :
    (toOccurrenceObservedGame root).InfoAction
      (0 : Player) secondOcc :=
  ⟨GameTree.Leaf alternativePayoff,
    List.mem_cons_of_mem (GameTree.Leaf leafPayoff)
      List.mem_cons_self⟩

/-- A genuinely occurrence-dependent strategy: choose the first child
everywhere except at `secondOcc`, where it chooses the alternative child. -/
noncomputable def separatingOccurrenceStrategy :
    (toOccurrenceObservedGame root).PureStrategy
      (0 : Player) := by
  classical
  intro information
  exact
    if h : information = secondOcc then
      h ▸ secondAlternativeAction
    else
      firstLegalAction information

@[simp]
theorem separatingOccurrenceStrategy_first :
    separatingOccurrenceStrategy firstOcc =
      (⟨.Leaf leafPayoff, List.mem_cons_self⟩ :
        (toOccurrenceObservedGame root).InfoAction
          (0 : Player) firstOcc) := by
  rw [separatingOccurrenceStrategy,
    dif_neg firstOcc_ne_secondOcc]
  rfl

@[simp]
theorem separatingOccurrenceStrategy_second :
    separatingOccurrenceStrategy secondOcc =
      secondAlternativeAction := by
  rw [separatingOccurrenceStrategy, dif_pos rfl]

/-- The occurrence strategy makes observably different child choices at the
two histories with the same endpoint subtree. -/
theorem separatingOccurrenceStrategy_distinguishes :
    (separatingOccurrenceStrategy firstOcc).1 ≠
      (separatingOccurrenceStrategy secondOcc).1 := by
  rw [separatingOccurrenceStrategy_first,
    separatingOccurrenceStrategy_second]
  intro heq
  have hpayoff :
      leafPayoff = alternativePayoff :=
    GameTree.Leaf.inj heq
  have hatZero :=
    congrFun hpayoff (0 : Player)
  norm_num [leafPayoff, alternativePayoff] at hatZero

/-- Every endpoint strategy lifted through the canonical refinement makes the
same choice at both occurrences, because endpoint information has merged
them. -/
theorem endpointLift_same_choice
    (strategy :
      (toObservedGame root).PureStrategy
        (0 : Player)) :
    (liftEndpointPureStrategy root 0 strategy firstOcc).1 =
      (liftEndpointPureStrategy root 0 strategy secondOcc).1 := by
  unfold liftEndpointPureStrategy
  change
    (strategy (forgetOccurrenceInfo root 0 firstOcc)).1 =
      (strategy (forgetOccurrenceInfo root 0 secondOcc)).1
  rw [forgetOccurrenceInfo_merges]

/-- Merged decision occurrences obstruct every strict observed-game isomorphism
from the endpoint compiler to the occurrence compiler, not only the canonical
occurrence-forgetting map.

An `ObservedGame.Iso` supplies an equivalence of complete histories together
with `map_infoAt`. The endpoint compiler assigns equal information states to
the two merged histories, while occurrence information determines its history,
so the two histories would have to coincide. -/
theorem not_nonempty_iso_toOccurrenceObservedGame_of_merged_histories
    {N U : Type*}
    (treeRoot : GameTree N U) (i : N)
    (first second :
      (toExtensiveGame treeRoot).toArena.HistoryFrom treeRoot)
    (hfirst : (toExtensiveGame treeRoot).mover first.1 = some i)
    (hsecond : (toExtensiveGame treeRoot).mover second.1 = some i)
    (hendpoint : first.1 = second.1)
    (hdifferent : first ≠ second) :
    ¬ Nonempty
        ((toObservedGame treeRoot).Iso
          (toOccurrenceObservedGame treeRoot)) := by
  rintro ⟨e⟩
  have htfirst :
      (toOccurrenceObservedGame treeRoot).base.mover
          (e.historyIso.stateEquiv first).1 = some i :=
    (e.map_mover first).trans hfirst
  have htsecond :
      (toOccurrenceObservedGame treeRoot).base.mover
          (e.historyIso.stateEquiv second).1 = some i :=
    (e.map_mover second).trans hsecond
  have hinfo :
      (toObservedGame treeRoot).infoAt first i hfirst =
        (toObservedGame treeRoot).infoAt second i hsecond :=
    forgetOccurrenceInfo_eq_of_endpoint_eq treeRoot i
      ⟨first, hfirst⟩ ⟨second, hsecond⟩ hendpoint
  have hmapped :
      (toOccurrenceObservedGame treeRoot).infoAt
          (e.historyIso.stateEquiv first) i htfirst =
        (toOccurrenceObservedGame treeRoot).infoAt
          (e.historyIso.stateEquiv second) i htsecond := by
    rw [← e.map_infoAt first i hfirst htfirst,
      ← e.map_infoAt second i hsecond htsecond, hinfo]
  exact hdifferent
    (e.historyIso.stateEquiv.injective
      (toOccurrenceObservedGame_hasSingletonInformation treeRoot i
        _ _ htfirst htsecond hmapped))

/-- **N-1B.** No strict observed-game isomorphism from the endpoint compiler to
the occurrence compiler exists for this concrete tree.

This conclusion does not follow merely from
`forgetOccurrenceInfo_not_injective`: it rules out every candidate strict
isomorphism by the separate merged-history argument above. It prevents the
false generalization that a directional information refinement must be a
strict relabeling, while retaining the positive refinement certificate below.
The statement is directional and makes no claim about all compiler inputs. -/
theorem not_nonempty_iso :
    ¬ Nonempty
        ((toObservedGame root).Iso
          (toOccurrenceObservedGame root)) :=
  not_nonempty_iso_toOccurrenceObservedGame_of_merged_histories
    root 0 ⟨repeated, directHistory⟩ ⟨repeated, viaMiddleHistory⟩
    rfl rfl rfl
    (fun heq => firstOcc_ne_secondOcc (Subtype.ext heq))

/-- The endpoint compiler is concretely certified as the information-coarsened
source and the occurrence compiler as its directional refinement. -/
theorem endpointOccurrenceRefinement_exists :
    Nonempty
      ((toObservedGame root).InformationRefinement
        (toOccurrenceObservedGame root)) :=
  ⟨endpointInformationRefinement root⟩

end Examples.OccurrenceNonIso
