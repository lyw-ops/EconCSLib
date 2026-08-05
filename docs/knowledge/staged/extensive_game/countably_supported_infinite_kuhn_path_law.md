---
id: game_theory.extensive_game.imperfect_information.countably_supported_infinite_kuhn_path_law
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.imperfect_information
title: Countably Supported Infinite Kuhn Path-Law Realization
kind: proof-plan
status: staged
target: game_theory.extensive_game.imperfect_information.perfect_recall_mixed_to_behavioral
plan_status: blocked
uses:
  - game_theory.extensive_game.imperfect_information.perfect_recall
verification:
  statement: accepted
  proof: gap
tags:
  - extensive-game
  - infinite-horizon
  - kuhn-theorem
  - path-law
  - projective-limit
---

# Countably Supported Infinite Kuhn Path-Law Realization

## Target

For a finite player set, discrete chance, countably supported mixed plans, and
an explicit recall certificate, identify the complete infinite path law of a
mixed profile with that of its root-conditioned behavioralization.

## Existing formal base

`ObservedChanceGame.countablySupportedMixedToBehavioral_boundedHistoryLaw`
proves equality of the stopped complete-history PMF for every finite fuel and
does not require finite information-state carriers.

## Missing lemma

The library does not yet prove that those root-conditioned finite laws form
the same projective family as the analytic/discrete infinite path executor.
A minimal missing statement is:

> If two certified absorbing history-policy executions have equal
> complete-history distributions at every finite fuel, then their induced
> complete-path measures are equal.

The proof must match the exact coordinate encoding and sigma algebra of
`Execution.InfiniteTrajectory`/`Observed.InfiniteExecution`; equality of
terminal marginals is insufficient.

## Proof plan

1. Express each path cylinder as a measurable event determined by a finite
   complete-history coordinate.
2. rewrite its probability through the corresponding bounded execution law;
3. apply the existing bounded mixed-to-behavioral equality;
4. prove equality on the generating cylinder π-system; and
5. conclude equality of path measures by the available uniqueness theorem.

For arbitrary (non-PMF) pure-strategy measures, first discharge the separate
measurable-evaluation and disintegration plan in
`arbitrary_measure_pure_strategy_realization.md`.

## References

- [Kuhn 1953, §4 and Thm. 4] H. W. Kuhn, “Extensive Games and the Problem of Information.” The original equivalence is finite; the projective-limit step above is an additional infinite-path argument.
