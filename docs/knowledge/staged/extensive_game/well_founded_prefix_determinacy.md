---
id: game_theory.extensive_game.perfect_information.well_founded_prefix_determinacy
primary_topic: game_theory.extensive_game
topics:
  - game_theory.extensive_game
  - game_theory.extensive_game.perfect_information
title: Well-Founded Prefix Determinacy
kind: theorem
status: staged
uses:
  - game_theory.extensive_game.perfect_information.determined_game
verification:
  statement: accepted
  proof: accepted
lean:
  declarations:
    - ExtensiveGame.ControlledObservedGame.WellFoundedTwoPlayerHypotheses.isTwoPlayerDetermined
    - ExtensiveGame.ControlledObservedGame.WellFoundedPrefixHypotheses.isTwoPlayerDetermined
tags:
  - backward-induction
  - determinacy
  - extensive-game
  - perfect-information
  - well-founded
---

# Well-Founded Prefix Determinacy

Let an observed logical game have exactly two players, no chance nodes,
perfect information, a total and exclusive complete-play winning condition,
and a well-founded legal-history child relation. Assume every declared
information state is represented and player-labelled histories have a legal
action. Then one of the two players has a total information-indexed pure
strategy that wins against every compatible opponent play.

The stronger prefix package additionally records a persistent, sound
prefix-decision certificate. It specializes to the same well-founded theorem.

## Formal route

`WellFounded.fix` assigns a winner to every complete history. At a terminal
history it reads the zero-sum winner from the canonical stuttering replay. At
a decision history the mover wins if some child is winning for that mover;
otherwise the other player wins.

Classical choice selects winning children and one concrete representative of
each information state. Perfect information identifies that representative
with the actual complete-history occurrence. Along the extracted strategy,
the root winner is invariant. Root well-foundedness makes every compatible
complete play eventually terminal, where the replay agrees with that play.

The proof uses classical choice and excluded middle. It uses neither
descriptive-set theory nor an arbitrary-set determinacy principle.

## Boundary

This theorem does not apply to a legal infinite branch. It also does not imply
open, closed, Borel, arbitrary-set, probabilistic, or almost-sure
determinacy. Gale--Stewart-style infinite determinacy remains a separate
theorem track.

## References

- [Zermelo 1913] Ernst Zermelo, “Über eine Anwendung der Mengenlehre auf die
  Theorie des Schachspiels.” Finite terminating perfect-information
  backward-determinacy precedent.
- [Gale--Stewart 1953] David Gale and F. M. Stewart, “Infinite Games with
  Perfect Information,” pp. 245--266. Source boundary for the distinct
  infinite-game determinacy theory.
