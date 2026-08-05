# Prompt 10 — Build a Sequential-Equilibrium Foundation

You are working in the EconCSLib repository. Design and implement the first
mathematically honest sequential-equilibrium layer for observed EFGs.

## Current carrier scope

Read `docs/design/efg-minimal-core-freeze.md`. Beliefs, assessments,
perturbations, consistency, and rationality are downstream data/certificates.
No repository-wide carrier freeze is active, but this task does not add them
to a carrier or to `Interface.StructuralCore`.

## Initial scope

Target finite observed EFGs with finite players/actions/information, explicit
chance laws, perfect recall, and a complete lawful subgame/information
presentation. Do not begin with arbitrary infinite or non-atomic games.

## Required work

1. Review authoritative definitions of:

   - behavioral profiles;
   - completely mixed profiles;
   - beliefs at information sets;
   - assessments;
   - Bayes consistency on reached information sets;
   - consistency as a limit of completely mixed assessments; and
   - sequential rationality.

2. Map those definitions onto `ControlledObservedGame` information states and
   the existing finite/chance/behavioral execution. Decide explicitly how
   unrepresented information states are excluded or witnessed.

3. Write the proposed Lean signatures and mathematical invariants in a staged
   knowledge node before implementation. Separate:

   - raw belief data;
   - normalized belief certificates;
   - an assessment;
   - consistency; and
   - sequential rationality.

4. Implement a minimal finite carrier/API with assumptions attached at the
   definition or theorem that needs them. Reuse Mathlib finite probability and
   topology rather than encoding convergence ad hoc.

5. Prove foundational implications that are actually valid, such as
   sequential equilibrium implying sequential rationality and consistency,
   and under the stated perfect-recall finite hypotheses the appropriate
   equilibrium consequence. State whether that consequence is Nash, weak
   sequential equilibrium, or standard SPE; do not conflate them.

6. Provide a small signaling or entry-deterrence example where off-path beliefs
   matter. The example must distinguish sequential equilibrium from merely
   checking on-path best responses.

7. Add a new opt-in facade only if the API is coherent enough for reuse.
   Otherwise keep it out of the stable aggregate and document promotion
   criteria.

## Mathematical guardrails

- Beliefs are indexed by information sets and histories within them, not just
  endpoint states.
- Bayes' rule alone does not define beliefs at zero-probability information
  sets.
- Consistency is a perturbation/limit property, not an arbitrary belief
  assignment.
- Standard SPE and sequential equilibrium are different concepts.

## Acceptance criteria

- The representation handles occurrence-sensitive histories and off-path
  information sets.
- Every probability normalization and convergence claim is proved.
- The example demonstrates a genuine belief-dependent distinction.
- No placeholder theorem or overbroad implication is introduced.
- Full builds, examples, knowledge checks, governance, placeholders, and
  whitespace checks pass.
