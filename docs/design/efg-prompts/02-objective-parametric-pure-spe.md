# Prompt 02 — Objective-Parametric Total Pure Standard SPE

You are working in the EconCSLib repository. Add a canonical operational route
from history-sensitive terminal/path objectives to total pure standard
subgame-perfect equilibrium.

## Current carrier scope

Read `docs/design/efg-minimal-core-freeze.md`. No repository-wide carrier
freeze is active, but this task keeps objectives and equilibrium downstream.
Do not modify the three carrier declarations or `Interface.StructuralCore`;
report any contrary representation evidence back to the core review.

## Problem

`Execution.Objective` supports `TerminalOutcome` and `PathOutcome`, while the
established total pure standard-SPE route in `Observed/SPE.lean` is centered on
the state-payoff `ObservedGame`. The generic
`ControlledObservedGame.ContinuationSemantics` is intentionally
evaluator-relative and must not be relabeled as operational standard SPE.

## Required work

1. Audit `Execution.Objective`, `Observed.Controlled.Infrastructure.Core`,
   `Observed.Controlled.Semantics`, `Observed.Game`, `Observed.SPE`, and the
   relevant `GameForm` continuation API.

2. Design the smallest downstream operational interface that:

   - executes a `ControlledObservedGame.PureProfile` from an accumulated
     complete history;
   - uses `ControlledGame.NoChanceOnHistories`;
   - consumes explicit total-termination evidence;
   - evaluates a root-relative or global history-sensitive
     `Arena.TerminalOutcome` and, where mathematically sound, a
     `Arena.PathOutcome`; and
   - produces a `GameForm` whose deviations are the canonical full pure
     strategy deviations.

3. Define lawful-system and complete-system equilibrium predicates with names
   that distinguish:

   - Nash on presentation-designated roots;
   - subgame perfection on an explicit lawful `SubgameSystem`; and
   - standard SPE on a `CompleteSubgameSystem`.

4. Prove the expected projection theorems: standard SPE implies SPE on the
   underlying system, Nash at the initial root, and Nash at every lawful root.

5. Prove a specialization theorem connecting the new objective-parametric
   semantics to the existing state-payoff semantics when the objective is
   induced by endpoint payoff. Prefer theorem-level compatibility over a
   second copied equilibrium hierarchy.

6. Add strict-iso/refinement preservation only for the exact objective
   compatibility hypotheses actually needed. Do not infer preservation from a
   structural map alone.

7. Expose the API through the narrowest appropriate objective/equilibrium
   facade and add import-boundary examples.

## Mathematical guardrails

- A terminal objective on histories must see the accumulated prefix; do not
  accidentally evaluate only a re-rooted suffix.
- A path objective must specify how a continuation play is embedded into the
  original root play.
- Total semantics must not return an arbitrary default for nontermination
  without an explicit construction and theorem.
- An arbitrary caller-defined evaluator remains evaluator-relative.
- A designated root is not automatically a lawful subgame root.

## Acceptance criteria

- A small regression demonstrates two terminal histories with the same
  endpoint but different objective values and shows that the continuation
  game forms distinguish them.
- Another regression proves specialization to an ordinary endpoint-payoff
  game.
- No carrier or structural-facade change occurs within this task's scope.
- Module docstrings state exact operational semantics and hypotheses.
- Full EFG builds, examples, placeholder checks, governance, and whitespace
  checks pass.
