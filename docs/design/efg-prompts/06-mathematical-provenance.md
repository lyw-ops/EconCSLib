# Prompt 06 — Strengthen Mathematical Provenance

You are working in the EconCSLib repository. Audit the mathematical
correctness and literature provenance of the EFG stack.

## Current carrier scope

Read `docs/design/efg-minimal-core-freeze.md`. This is a documentation and
theorem-review task; it does not authorize carrier or StructuralCore changes.
No repository-wide carrier freeze is implied by this task scope.

## Problem

The code documents internal architecture well, but many mathematically
substantive declarations lack precise literature anchors. This makes it hard
to distinguish standard definitions, library-specific generalizations,
representation theorems, and intentionally weaker finite approximations.

## Required work

1. Inventory exported definitions/theorems in:

   - information and recall;
   - subgames and SPE;
   - mixed/behavioral/general strategies and Kuhn results;
   - winning and determinacy;
   - path laws, conditioning, and restart;
   - refinement/simulation/preservation; and
   - frontend compilation.

2. Classify each substantive item as:

   - standard textbook definition/result;
   - standard result under nonstandard representation;
   - EconCSLib-specific abstraction;
   - finite/bounded approximation;
   - preservation theorem; or
   - open or deliberately unformalized generalization.

3. Consult primary or authoritative sources. Record exact theorem/section
   labels and the hypotheses that correspond to the Lean statement. Do not
   cite a broad chapter as support for a materially stronger theorem.

4. Add concise module/declaration docstrings with reference labels. Register
   recurring sources in `docs/knowledge/mdblueprint.yml` with lawful external
   links. Do not add PDFs, scans, OCR text, or long quotations.

5. Where a Lean name overstates the literature-backed claim, either:

   - strengthen the hypotheses/proof to match the name;
   - rename during pre-stability with a migration note; or
   - explicitly document the weaker semantics.

6. Add staged knowledge nodes for mathematically important gaps rather than
   placeholder Lean theorems. Keep provenance metadata out of scholarly
   `## References`.

7. Produce a provenance matrix with columns:
   declaration, source, source hypotheses, Lean hypotheses, representation
   translation, verification status, and gap.

## Acceptance criteria

- Every flagship EFG theorem has a precise source or is explicitly labeled as
  a library-specific result.
- No citation is used to justify missing assumptions.
- Finite, countable/discrete, and analytic/non-atomic claims are kept distinct.
- Designated continuation equilibrium is not cited as standard SPE.
- Knowledge-reference checks, blueprint checks, Lean builds, placeholder
  checks, governance, and `git diff --check` pass.
