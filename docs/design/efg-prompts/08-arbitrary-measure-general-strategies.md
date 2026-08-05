# Prompt 08 — Arbitrary-Measure General Strategies

You are working in the EconCSLib repository. Extend the strategy semantics
beyond countably supported PMF mixtures without calling a discrete carrier
fully general.

## Current carrier scope

Read `docs/design/efg-minimal-core-freeze.md`. No repository-wide carrier
freeze is active, but this task keeps measure theory and randomized strategy
semantics downstream and does not modify carriers or `Interface.StructuralCore`.

## Problem

The current general/mixed strategy route is fundamentally discrete or
countably supported. An arbitrary probability measure over pure strategies,
and its relationship to behavioral measurable kernels, needs measurable
strategy spaces and cannot be obtained by renaming `PMF`.

## Required work

1. Audit `Observed.General`, `Observed.Mixed`, `Observed.Behavior`,
   `Observed.Kuhn*`, the analytic execution/presentation modules, and relevant
   Mathlib `Measure`/`ProbabilityMeasure` APIs.

2. Write a theorem-design note before Lean code that fixes:

   - the measurable space on each dependent pure-strategy carrier;
   - whether randomization is independent by player or a joint/correlated
     profile law;
   - evaluation measurability;
   - the path-law construction used for outcomes;
   - the exact relationship to behavioral kernels; and
   - finite/countable specializations.

3. Add the smallest honest arbitrary-measure carrier and semantics. Reuse
   Mathlib probability-measure structures where possible. Do not assume all
   function spaces have a useful measurable structure automatically.

4. Prove embeddings from pure and countably supported PMF strategies and show
   that the new semantics agrees with the existing discrete semantics on those
   embeddings.

5. State realization/equivalence with behavioral strategies only under the
   measurable, recall, standard-Borel, independence, and regular-conditional
   hypotheses actually used. If Mathlib lacks a required theorem, isolate the
   missing lemma as a staged knowledge node rather than an axiom.

6. Place the API in an analytic equilibrium facade, not the discrete facade,
   unless the declaration is genuinely measure-agnostic.

## Mathematical guardrails

- “General strategy” must say whether it means a probability measure over
  pure strategies, a correlated law over profiles, or an arbitrary stochastic
  process.
- Product measures over dependent, possibly uncountable function spaces are
  not free.
- Equality of terminal distributions is weaker than equality of complete path
  laws.
- Kuhn equivalence needs a precise recall and conditioning theorem.

## Acceptance criteria

- The API name explicitly distinguishes arbitrary measures from PMFs.
- Pure and PMF embeddings have proved semantic compatibility.
- No unrestricted measurable realization theorem is claimed.
- At least one non-countably-supported example typechecks or the exact Mathlib
  blocker is documented with a minimal reproducible statement.
- Analytic/discrete facade boundaries, builds, governance, placeholders,
  knowledge checks, and whitespace checks pass.
