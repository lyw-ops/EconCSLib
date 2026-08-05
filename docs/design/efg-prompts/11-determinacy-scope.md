# Prompt 11 — Separate and Extend Determinacy Scopes

You are working in the EconCSLib repository. Clarify the boundary between
constructive finite-game determinacy and infinite winning-game determinacy,
then implement the next justified layer.

## Current carrier scope

Read `docs/design/efg-minimal-core-freeze.md`. Winning conditions and
determinacy assumptions remain downstream. No repository-wide carrier freeze
is active, but this task does not modify carriers or `Interface.StructuralCore`.

## Problem

The library has finite/well-founded winning results and path-winning
interfaces. These must not be read as unrestricted determinacy for arbitrary
infinite winning sets. Borel/open/closed determinacy involves materially
different mathematics and possibly stronger foundational assumptions.

## Required work

1. Inventory all declarations containing `Determina*`, winning strategies,
   quasistrategies, backward induction, and almost-sure winning.

2. Produce a scope table with:

   - number of players and zero-sum assumptions;
   - perfect versus imperfect information;
   - chance versus no chance;
   - finite/well-founded versus infinite play;
   - payoff/winning-set complexity;
   - pure versus randomized strategies;
   - constructive/classical principles used; and
   - exact conclusion.

3. Rename or document any declaration whose name can be mistaken for a
   stronger determinacy theorem than its hypotheses justify.

4. Review primary sources and choose one next theorem that fits the existing
   representation. Candidate scopes include finite well-founded determinacy,
   open games on a countable tree, or a clearly axiomatized external
   determinacy principle. Do not silently assume arbitrary-set determinacy.

5. Before Lean implementation, identify whether the proof needs transfinite
   recursion, descriptive set theory, choice, excluded middle, or a theorem
   absent from Mathlib. Record those foundations explicitly.

6. Implement only a theorem with a complete route. Otherwise add a
   source-backed staged proof plan and improve the public scope documentation.

7. Add examples/counterexamples showing why the finite theorem does not imply
   the unrestricted infinite statement.

## Acceptance criteria

- Every public determinacy claim has an unambiguous scope.
- Logical, probabilistic, and almost-sure winning are not conflated.
- No arbitrary-set or Borel determinacy theorem is inferred from finite
  backward induction.
- Any new assumption principle is explicit in the theorem statement or
  imported theorem, with its foundational strength documented.
- Lean/knowledge builds, governance, placeholder checks, and whitespace checks
  pass.
