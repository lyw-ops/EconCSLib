/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.FiniteObservation

/-!
# Effective path laws from coherent finite prefixes

An effective path law exposes an exact `FiniteLaw` for every requested finite
horizon.  Its coherence proof says that extending execution and then
forgetting the new coordinates preserves the semantic finite law at the
earlier horizon.  Coherence uses `FiniteLaw.Equivalent`, because a later
finite-law presentation can split one earlier atom into several occurrences
with the same total weight.

The state and event variants below retain the absolute policy clock and the
whole supplied prefix.  Root laws are their time-zero specializations.  The
query interface contains only finite laws, exact rational masses, finite
coordinates, and Boolean cylinder predicates.  It does not expose an
infinite path, a measure, or an arbitrary measurable set.

Computing horizon `steps` expands the same exact finite execution tree as
`prefixLawFrom`.  Runtime and output size are therefore proportional to its
weighted occurrence list and can grow exponentially with the horizon and
branching degree.  This layer proves projective consistency; it deliberately
does not merge duplicate atoms or decide tail events.

## Main definitions

* `StateEffectivePathLawFrom` and `EventEffectivePathLawFrom`;
* `StateHistoryPolicy.effectivePathLawFrom` and
  `EventHistoryPolicy.effectivePathLawFrom`;
* `coordinateLaw` for exact coordinate marginals;
* `cylinderMass` for exact Boolean finite-prefix queries;
* `cylinderMass_extend` and `coordinateLaw_extend` for query coherence.
-/

namespace KernelArena

universe uS uA

private theorem map_const_equivalent_pure {α β : Type*}
    (law : FiniteLaw α) (target : β) :
    (law.map fun _ => target).Equivalent (FiniteLaw.pure target) := by
  intro value
  change
    (law.map fun _ => target).expectRat value =
      (FiniteLaw.pure target).expectRat value
  rw [FiniteLaw.expectRat_map, FiniteLaw.expectRat_pure]
  exact FiniteLaw.expectRat_const law (value target)

/-- A coherent family of exact state-prefix laws extending one supplied
prefix while retaining its absolute clock.  The argument to `prefixLaw` is
the number of new transitions, so its absolute horizon is `start + steps`. -/
structure StateEffectivePathLawFrom (A : KernelArena) (start : ℕ)
    (initialPrefix : A.StatePrefix start) where
  /-- Exact state-prefix law after the requested number of transitions. -/
  prefixLaw : (steps : ℕ) → FiniteLaw (A.StatePrefix (start + steps))
  /-- At zero new transitions the supplied prefix is deterministic. -/
  prefixLaw_zero : prefixLaw 0 = FiniteLaw.pure initialPrefix
  /-- Later laws restrict semantically to every earlier requested law. -/
  coherent : ∀ (earlier extra : ℕ),
    ((prefixLaw (earlier + extra)).map fun history =>
      StatePrefix.truncate history (start + earlier) (by omega)).Equivalent
        (prefixLaw earlier)

end KernelArena
