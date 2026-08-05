/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Winning

/-!
# Logical winning import boundary

The winning facade exposes winning conditions, pure/quasi winning strategies,
determinacy predicates, and explicit finite/well-founded hypothesis packages.
It does not import stochastic path laws or analytic kernels.
-/

#check Arena.WinningConditionFrom.IsTwoPlayerZeroSum
#check ExtensiveGame.ControlledObservedGame.HasPathwiseWinningStrategy
#check ExtensiveGame.ControlledObservedGame.IsTwoPlayerDetermined
#check ExtensiveGame.ControlledObservedGame.FiniteTwoPlayerHypotheses
#check ExtensiveGame.ControlledObservedGame.FiniteTwoPlayerHypotheses.isTwoPlayerDetermined
#check ExtensiveGame.ControlledObservedGame.WellFoundedTwoPlayerHypotheses
#check ExtensiveGame.ControlledObservedGame.WellFoundedTwoPlayerHypotheses.isTwoPlayerDetermined
#check ExtensiveGame.ControlledObservedGame.WellFoundedPrefixHypotheses
#check ExtensiveGame.ControlledObservedGame.WellFoundedPrefixHypotheses.isTwoPlayerDetermined
#check ExtensiveGame.ObservedGame.HasPathwiseWinningStrategy
#check ExtensiveGame.ObservedGame.HasPureProfileExtension
#check ExtensiveGame.ObservedGame.HasStrategicWinningStrategy
#check ExtensiveGame.ObservedGame.EveryCompatiblePlayRealizableByPureProfile
#check ExtensiveGame.ObservedGame.HasWinningQuasiStrategy
#check ExtensiveGame.ObservedGame.HasSomePathwiseWinningStrategy
#check ExtensiveGame.ObservedGame.IsTwoPlayerDetermined
#check ExtensiveGame.ObservedGame.FiniteTwoPlayerHypotheses
#check ExtensiveGame.ObservedGame.WellFoundedPrefixHypotheses

/--
error: Unknown constant `ExtensiveGame.ObservedGame.HasWinningStrategy`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.HasWinningStrategy

/--
error: Unknown constant `ExtensiveGame.ObservedGame.WinningStrategies`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.WinningStrategies

/--
error: Unknown constant `ExtensiveGame.ObservedGame.IsDetermined`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.IsDetermined

/--
error: Unknown constant `ExtensiveGame.ObservedGame.isDetermined_of_hasWinningStrategy`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.isDetermined_of_hasWinningStrategy

/--
error: Unknown constant `ExtensiveGame.ObservedGame.isDetermined_iff_isTwoPlayerDetermined`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.isDetermined_iff_isTwoPlayerDetermined

/--
error: Unknown constant `ExtensiveGame.ObservedGame.not_both_haveWinningStrategy`
-/
#guard_msgs in
#check ExtensiveGame.ObservedGame.not_both_haveWinningStrategy

/--
error: Unknown constant `Arena.pathLaw`
-/
#guard_msgs in
#check Arena.pathLaw

/--
error: Unknown identifier `MeasurableKernelArena`
-/
#guard_msgs in
#check MeasurableKernelArena
