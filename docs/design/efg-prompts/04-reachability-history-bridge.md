# Prompt 04 — Complete the Reachability/History Bridge

You are working in the EconCSLib repository. Make the relationship between
propositional reachability and occurrence-sensitive typed histories explicit,
mathematically correct, and reusable.

## Current carrier scope

Read `docs/design/efg-minimal-core-freeze.md`. No repository-wide carrier
freeze is active, but this bridge task does not change carrier declarations or
the current `Interface.StructuralCore` boundary. You may add derived
declarations to an existing structural owner module without growing that
boundary.

## Problem

`Arena.History.toReachable` forgets a concrete action history. The public API
does not expose the converse existence theorem prominently enough, so clients
repeat conversions or conflate a proof-irrelevant reachability proposition
with a path witness.

## Required work

1. Inspect all uses of `Arena.Reachable`, `Arena.History`,
   `Arena.HistoryFrom`, subgame roots, continuation roots, and compiler
   occurrence states.

2. Add the canonical theorem in `Structural.History`:

   ```lean
   A.Reachable start finish ↔ Nonempty (A.History start finish)
   ```

   or the orientation best aligned with Mathlib naming. Construct the reverse
   implication without changing `Reachable` from `Prop` to `Type`.

3. If downstream code needs an actual witness, add a clearly
   `noncomputable` choice function derived from the existence theorem. Do not
   claim an `Equiv` between reachability proofs and histories: proof
   irrelevance collapses the former while multiple histories may reach the
   same endpoint.

4. Add simp/round-trip lemmas only where they state a true proposition. In
   particular, a chosen history need not equal an arbitrary original history.

5. Replace local ad hoc existence proofs and conversions where doing so
   materially simplifies continuation, subgame, or compiler code.

6. Add a diamond regression: two distinct histories reach the same endpoint,
   both forget to the same reachability proposition, and the history
   occurrences remain distinguishable.

7. Document when an API should accept:

   - `Reachable` for endpoint existence;
   - `History` for a specific path;
   - `HistoryFrom` for an occurrence state.

## Acceptance criteria

- The public theorem gives both logical directions.
- No false inverse/equivalence of proof objects is introduced.
- The diamond regression preserves occurrence sensitivity.
- The change adds no dependency outside the five-module StructuralCore
  closure.
- Focused and full builds, examples, placeholder checks, governance, and
  whitespace checks pass.
