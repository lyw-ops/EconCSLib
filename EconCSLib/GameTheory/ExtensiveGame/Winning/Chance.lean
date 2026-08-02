/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.InfiniteTrajectory
import EconCSLib.GameTheory.ExtensiveGame.Winning.Basic

/-!
# Almost-sure winning under discrete infinite path laws

Pathwise robust winning and almost-sure winning are different solution
concepts. `HasPathwiseWinningStrategy` universally quantifies over opponent
and nature moves. This module instead fixes a probability law on ambient
history paths and asks that almost every sampled path be legal and winning.

The probability measure remains on the ordinary function space used by
Ionescu--Tulcea. A sample is bundled into `CompletePlayFromHistory` only after
supplying the common unbundled legality predicate. No measurable structure on
the dependent bundled play type is assumed.
-/

open MeasureTheory

namespace Arena

variable {A : Arena} {start : A.State}
  {current : A.HistoryFrom start} {N : Type*}

namespace WinningConditionFrom

/-- The ambient function-space event consisting of legal paths won by player
`i`. This is the event tested by the almost-sure winning predicates below. -/
def winningPathEvent
    (W : A.WinningConditionFrom current N)
    (i : N) :
    Set (ℕ → A.HistoryFrom start) :=
  {path |
    ∃ hlegal : A.IsCompletePlayPathFrom current path,
      CompletePlayFromHistory.ofPath path hlegal ∈ W i}

/-- The legal winning-path event for player `i` is measurable in the supplied
ambient path sigma-algebra. -/
def IsMeasurableWinningPathEvent
    [MeasurableSpace (A.HistoryFrom start)]
    (W : A.WinningConditionFrom current N)
    (i : N) : Prop :=
  MeasurableSet (W.winningPathEvent i)

/-- Almost-everywhere winning for an arbitrary measure on ambient
complete-history paths.

Illegal paths do not count as winning. For canonical stochastic execution,
`pathLaw_ae_isCompletePlayPathFrom` supplies legality almost everywhere.

This deliberately does not call the law probabilistic: in particular the zero
measure makes every almost-everywhere statement true. Use
`IsAlmostSurelyWinningUnder` when the law is known to have total mass one. -/
def AEWinningUnder
    [MeasurableSpace (A.HistoryFrom start)]
    (W : A.WinningConditionFrom current N)
    (law : Measure (ℕ → A.HistoryFrom start))
    (i : N) : Prop :=
  ∀ᵐ path ∂law, path ∈ W.winningPathEvent i

/-- Almost-everywhere winning is monotone in the selected player's winning
set. -/
theorem AEWinningUnder.mono
    [MeasurableSpace (A.HistoryFrom start)]
    {W V : A.WinningConditionFrom current N}
    {law : Measure (ℕ → A.HistoryFrom start)}
    {i : N}
    (hwinning : W.AEWinningUnder law i)
    (hsubset : W i ⊆ V i) :
    V.AEWinningUnder law i := by
  filter_upwards [hwinning] with path hpath
  rcases hpath with ⟨hlegal, hwins⟩
  exact ⟨hlegal, hsubset hwins⟩

/-- Almost-sure winning under a probability measure on ambient
complete-history paths.

The `IsProbabilityMeasure` assumption prevents the vacuity of arbitrary
measures such as the zero measure. -/
def IsAlmostSurelyWinningUnder
    [MeasurableSpace (A.HistoryFrom start)]
    (W : A.WinningConditionFrom current N)
    (law : Measure (ℕ → A.HistoryFrom start))
    [IsProbabilityMeasure law]
    (i : N) : Prop :=
  W.AEWinningUnder law i

/-- A measurable almost-sure winning certificate for an arbitrary probability
path measure. Measurability and probability-one winning are kept as separate
fields because neither follows from the other. -/
structure MeasurableAlmostSureWinningUnder
    [MeasurableSpace (A.HistoryFrom start)]
    (W : A.WinningConditionFrom current N)
    (law : Measure (ℕ → A.HistoryFrom start))
    [IsProbabilityMeasure law]
    (i : N) : Prop where
  /-- The legal winning-path event is measurable. -/
  measurable :
    W.IsMeasurableWinningPathEvent i
  /-- The probability measure assigns full mass to that event. -/
  almostSure :
    W.IsAlmostSurelyWinningUnder law i

/-- Almost-sure winning is monotone in the selected player's winning set. -/
theorem IsAlmostSurelyWinningUnder.mono
    [MeasurableSpace (A.HistoryFrom start)]
    {W V : A.WinningConditionFrom current N}
    {law : Measure (ℕ → A.HistoryFrom start)}
    [IsProbabilityMeasure law]
    {i : N}
    (hwinning : W.IsAlmostSurelyWinningUnder law i)
    (hsubset : W i ⊆ V i) :
    V.IsAlmostSurelyWinningUnder law i :=
  AEWinningUnder.mono hwinning hsubset

end WinningConditionFrom

/-- Almost-sure winning under the canonical infinite law of one stochastic
history policy. -/
def StochasticHistoryPolicy.IsAlmostSurelyWinning
    [(state : A.State) → Decidable (A.IsTerminal state)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start)
    (W : A.WinningConditionFrom current N)
    (i : N) : Prop :=
  W.IsAlmostSurelyWinningUnder
    (pathLaw policy current) i

/-- If player `i` wins every legal complete play, then every canonical
stochastic history policy is almost surely winning for `i`.

This is a support theorem, not a converse: a law may assign probability zero
to legal losing plays. -/
theorem StochasticHistoryPolicy.isAlmostSurelyWinning_of_forall
    [(state : A.State) → Decidable (A.IsTerminal state)]
    [MeasurableSpace (A.HistoryFrom start)]
    [MeasurableSingletonClass (A.HistoryFrom start)]
    [Countable (A.HistoryFrom start)]
    (policy : A.StochasticHistoryPolicy start)
    (current : A.HistoryFrom start)
    (W : A.WinningConditionFrom current N)
    (i : N)
    (hwins :
      ∀ play : A.CompletePlayFromHistory current,
        play ∈ W i) :
    policy.IsAlmostSurelyWinning current W i := by
  filter_upwards
    [pathLaw_ae_isCompletePlayPathFrom policy current]
      with path hlegal
  exact
    ⟨hlegal,
      hwins
        (CompletePlayFromHistory.ofPath path hlegal)⟩

end Arena
