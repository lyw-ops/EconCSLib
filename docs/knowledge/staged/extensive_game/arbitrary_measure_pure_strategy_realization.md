---
id: game_theory.extensive_game.imperfect_information.arbitrary_measure_pure_strategy_realization
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.imperfect_information
title: Arbitrary-Measure Pure-To-Behavioral Realization Boundary
kind: proof-plan
status: staged
target: game_theory.extensive_game.imperfect_information.perfect_recall_mixed_to_behavioral
plan_status: blocked
uses:
  - game_theory.extensive_game.imperfect_information.perfect_recall
  - game_theory.extensive_game.imperfect_information.mixed_behavioral_general_strategies
verification:
  statement: accepted
  proof: gap
tags:
  - extensive-game
  - probability-measure
  - perfect-recall
  - kuhn-theorem
  - standard-borel
---

# Arbitrary-Measure Pure-To-Behavioral Realization Boundary

## Target

Extend mixed-to-behavioral realization from countably supported finite PMFs to
a probability measure on a measurable space of complete pure strategies,
preserving the induced complete-path law.

## Required hypotheses

The measurable pure-strategy and profile spaces must be explicit. The result
also needs perfect recall, a standard-Borel/disintegration hypothesis for the
conditioning spaces, measurable action evaluation, and a declared convention
for playerwise independence versus a correlated joint profile law.

## Missing formal bridge

Mathlib supplies probability measures, pushforwards, kernels, and
standard-Borel disintegration tools, but EconCSLib does not yet have a theorem
assembling them for the dependent information-action function space of an
observed EFG. In particular, there is no proved measurable evaluator from an
arbitrary pure-strategy law to every information-set action, no compatible
infinite player/information product construction, and no telescoping theorem
showing equality of the resulting complete path laws.

## Proof plan

1. Restrict to a countable history presentation with standard-Borel
   information and action fibers.
2. Construct measurable evaluation maps for represented information states.
3. Disintegrate the pure-strategy law at each reached information state.
4. Use perfect recall to prove the conditional action kernels telescope along
   every finite history.
5. Apply uniqueness of the constructed path measure to obtain equality of
   complete path laws.
6. Recover the existing finite PMF theorem by identifying each discrete
   conditional measure with its PMF conditional.

## References

- [Kuhn 1953, §4 and Thm. 4] H. W. Kuhn, “Extensive Games and the Problem of Information.” The equivalence theorem is finite and assumes perfect recall; it does not by itself justify the arbitrary-measure extension above.
- [MFoGT, Thm. 6.3.4] Laraki, Renault, and Sorin, *Mathematical Foundations of Game Theory*. Mixed-to-behavioral outcome equivalence under perfect recall.
