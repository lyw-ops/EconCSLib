/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.DeferredSampling.Realization
import EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Execution
import EconCSLib.GameTheory.ExtensiveGame.Observed.SemanticMode
import EconCSLib.GameTheory.ExtensiveGame.Execution.Objective

/-!
# Complete-history-law equivalence for observed EFGs

This module makes the strongest currently executable semantic comparison the
primary one.  Bounded execution first produces a law on complete,
occurrence-sensitive histories.  Terminal-history, outcome, payoff, and
law-utility comparisons are then pushforwards of that law.

The API deliberately calls the one-way objects `Realization`, not `Iso`.
`CompleteHistoryLawRealization` maps every source strategy and therefore every
source unilateral deviation.  The separate `TargetDeviationsCoveredAt`
predicate records the additional reverse semantic coverage needed for
two-way equilibrium transfer.

The concrete models below are discrete: chance and strategic randomization
use `PMF`.  `StrategicMode.analyticGeneral` is only a classification tag for
future measurable semantics; no analytic strategy carrier is constructed or
claimed here.

## Main definitions

* `StrategicMode` and `ChanceSemantics`.
* `BoundedCompleteHistorySemantics`.
* `CompleteHistoryLawEquivalentAt`.
* `TerminalHistoryLawEquivalentAt`.
* `OutcomeLawEquivalentAt` and `PayoffLawEquivalentAt`.
* `CompleteHistoryLawRealization`.
* `CompleteHistoryLawRealization.TargetDeviationsCoveredAt`.

## Realization results

* finite no-absent-minded behavioral play is realized by independently
  sampled mixed contingent plans;
* finite perfect-recall mixed play is realized rootwise by conditional
  behavioral play;
* both results preserve terminal-history and payoff laws by pushforward.
-/

namespace ExtensiveGame.ObservedChanceGame

universe uN uU uAS uO uI uP uStrategy uOutcome uV

variable {N : Type uN} {U : Type uU}

/-- A bounded complete-history-law evaluator for one strategy class.

The result retains complete histories rather than endpoint states, so merged
world states do not identify distinct action occurrences. -/
structure BoundedCompleteHistorySemantics
    (G : ObservedChanceGame N U) where
  /-- One strategy carrier per player. -/
  Strategy : N → Type uStrategy
  /-- Classification of the strategy carrier. -/
  strategicMode : StrategicMode
  /-- Classification of the chance semantics. -/
  chanceSemantics : ChanceSemantics
  /-- Complete bounded law from every accumulated history. -/
  historyLaw :
    (∀ i, Strategy i) →
      G.observed.base.toArena.HistoryFrom G.observed.base.init →
      ℕ →
      PMF
        (G.observed.base.toArena.HistoryFrom
          G.observed.base.init)

namespace BoundedCompleteHistorySemantics

variable {G : ObservedChanceGame N U}

/-- Complete profiles for one history-law semantics. -/
abbrev Profile (S : G.BoundedCompleteHistorySemantics) :=
  ∀ i, S.Strategy i

/-- Equality of complete occurrence-sensitive history laws at one root and
one bounded horizon. -/
def CompleteHistoryLawEquivalentAt
    (S T : G.BoundedCompleteHistorySemantics)
    (source : S.Profile) (target : T.Profile)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (fuel : ℕ) : Prop :=
  S.historyLaw source current fuel =
    T.historyLaw target current fuel

/-- Equality after observing any function of the bounded complete history. -/
def OutcomeLawEquivalentAt
    (S T : G.BoundedCompleteHistorySemantics)
    (observer :
      (G.observed.base.toArena.HistoryFrom G.observed.base.init) →
        Outcome)
    (source : S.Profile) (target : T.Profile)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (fuel : ℕ) : Prop :=
  (S.historyLaw source current fuel).map observer =
    (T.historyLaw target current fuel).map observer

/-- Convert one bounded history to an optional terminal history.

`none` means the horizon ended at a nonterminal history; no artificial
terminal result is introduced. -/
def terminalHistoryAt
    (G : ObservedChanceGame N U)
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (history :
      G.observed.base.toArena.HistoryFrom G.observed.base.init) :
    Option
      (G.observed.base.toArena.TerminalHistoryFrom
        G.observed.base.init) :=
  if hterminal :
      G.observed.base.isTerminal history.1 then
    some ⟨history, hterminal⟩
  else
    none

/-- Equality of optional terminal-history laws. -/
def TerminalHistoryLawEquivalentAt
    (S T : G.BoundedCompleteHistorySemantics)
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (source : S.Profile) (target : T.Profile)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (fuel : ℕ) : Prop :=
  S.OutcomeLawEquivalentAt T
    (terminalHistoryAt G) source target current fuel

/-- Equality of the existing optional terminal-payoff laws. -/
def PayoffLawEquivalentAt
    (S T : G.BoundedCompleteHistorySemantics)
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (source : S.Profile) (target : T.Profile)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (fuel : ℕ) : Prop :=
  S.OutcomeLawEquivalentAt T
    G.stoppedPayoffAtHistory source target current fuel

/-- Equality under every player-indexed utility functional of the payoff law.

This includes expected utility when `utility` is expectation, but does not
hard-code linear preferences into the EFG semantics. -/
def LawUtilityEquivalentAt
    (S T : G.BoundedCompleteHistorySemantics)
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    (utility : PMF (Option (N → U)) → N → V)
    (source : S.Profile) (target : T.Profile)
    (current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init)
    (fuel : ℕ) : Prop :=
  ∀ i,
    utility
        ((S.historyLaw source current fuel).map
          G.stoppedPayoffAtHistory) i =
      utility
        ((T.historyLaw target current fuel).map
          G.stoppedPayoffAtHistory) i

/-- Root-presentation-wide complete-history-law equivalence. -/
def CompleteHistoryLawEquivalentOnRoots
    (S T : G.BoundedCompleteHistorySemantics)
    (roots : G.observed.RootPresentation)
    (source : S.Profile) (target : T.Profile) : Prop :=
  ∀ current, roots.IsRoot current →
    ∀ fuel, S.CompleteHistoryLawEquivalentAt T
      source target current fuel

/-- Continuation-wide complete-history-law equivalence. -/
def CompleteHistoryLawEquivalentOnAllContinuations
    (S T : G.BoundedCompleteHistorySemantics)
    (source : S.Profile) (target : T.Profile) : Prop :=
  S.CompleteHistoryLawEquivalentOnRoots T
    (ObservedGame.ContinuationRootPresentation.allHistories
      G.observed.base)
    source target

/-- Initial-root complete-history-law equivalence. -/
def CompleteHistoryLawEquivalentInitially
    (S T : G.BoundedCompleteHistorySemantics)
    (source : S.Profile) (target : T.Profile) : Prop :=
  S.CompleteHistoryLawEquivalentOnRoots T
    (ObservedGame.ContinuationRootPresentation.initialOnly
      G.observed.base)
    source target

/-- Complete-history equality implies equality of every ordinary pushforward
outcome law. -/
theorem CompleteHistoryLawEquivalentAt.mappedOutcome
    {S T : G.BoundedCompleteHistorySemantics}
    {source : S.Profile} {target : T.Profile}
    {current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init}
    {fuel : ℕ}
    (h : S.CompleteHistoryLawEquivalentAt T
      source target current fuel)
    (observer :
      (G.observed.base.toArena.HistoryFrom G.observed.base.init) →
        Outcome) :
    S.OutcomeLawEquivalentAt T observer
      source target current fuel := by
  unfold OutcomeLawEquivalentAt
  rw [h]

/-- Complete-history equality implies optional terminal-history-law
equality. -/
theorem CompleteHistoryLawEquivalentAt.terminalHistory
    {S T : G.BoundedCompleteHistorySemantics}
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    {source : S.Profile} {target : T.Profile}
    {current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init}
    {fuel : ℕ}
    (h : S.CompleteHistoryLawEquivalentAt T
      source target current fuel) :
    S.TerminalHistoryLawEquivalentAt T
      source target current fuel :=
  h.mappedOutcome (terminalHistoryAt G)

/-- Complete-history equality implies optional terminal-payoff-law equality.
-/
theorem CompleteHistoryLawEquivalentAt.payoff
    {S T : G.BoundedCompleteHistorySemantics}
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    {source : S.Profile} {target : T.Profile}
    {current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init}
    {fuel : ℕ}
    (h : S.CompleteHistoryLawEquivalentAt T
      source target current fuel) :
    S.PayoffLawEquivalentAt T source target current fuel :=
  h.mappedOutcome G.stoppedPayoffAtHistory

/-- Payoff-law equality implies equality under any law utility, including
expected utility where defined. -/
theorem PayoffLawEquivalentAt.utility
    {S T : G.BoundedCompleteHistorySemantics}
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)]
    {source : S.Profile} {target : T.Profile}
    {current :
      G.observed.base.toArena.HistoryFrom G.observed.base.init}
    {fuel : ℕ}
    (h : S.PayoffLawEquivalentAt T
      source target current fuel)
    (utility : PMF (Option (N → U)) → N → V) :
    S.LawUtilityEquivalentAt T utility
      source target current fuel := by
  intro i
  rw [h]

end BoundedCompleteHistorySemantics

/-- Behavioral discrete-PMF complete-history semantics. -/
noncomputable def behavioralCompleteHistorySemantics
    (G : ObservedChanceGame N U)
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)] :
    G.BoundedCompleteHistorySemantics where
  Strategy := G.observed.BehavioralStrategy
  strategicMode := .behavioral
  chanceSemantics := .discretePMF
  historyLaw profile current fuel :=
    G.observed.base.toArena.stochasticHistoryPMFFrom
      (BehavioralProfile.toHistoryPolicy G profile)
      current fuel

/-- Mixed discrete-PMF complete-history semantics. -/
noncomputable def mixedCompleteHistorySemantics
    (G : ObservedChanceGame N U)
    [Fintype N]
    [(state : G.observed.base.State) →
      Decidable (G.observed.base.isTerminal state)] :
    G.BoundedCompleteHistorySemantics where
  Strategy := G.observed.MixedStrategy
  strategicMode := .mixed
  chanceSemantics := .discretePMF
  historyLaw := G.mixedStoppedHistoryLawFrom

namespace BoundedCompleteHistorySemantics

variable {G : ObservedChanceGame N U}

/-- One-way exact realization of all source profiles by target profiles.

Because profiles are dependent products, `mapStrategy` acts componentwise and
therefore maps every source unilateral deviation while holding the opponents'
mapped strategies fixed. -/
