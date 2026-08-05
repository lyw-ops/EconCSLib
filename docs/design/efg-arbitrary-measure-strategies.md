# Arbitrary-Measure Pure-Strategy Laws

This note fixes the semantics of the first non-PMF strategy-law API before
its Lean implementation. It is subordinate to
[`efg-governance.md`](efg-governance.md) for architecture and to
[`efg-public-api.md`](efg-public-api.md) for import selection.

## Chosen carrier

`ObservedGame.PureProfileMeasurableModel` supplies, rather than infers:

- a measurable space on each dependent carrier `G.PureStrategy i`;
- a measurable space on `G.PureProfile`; and
- measurability of every player-coordinate projection.

`ArbitraryMeasurePureStrategy` is a `ProbabilityMeasure` on one player's
pure-strategy carrier. `ArbitraryMeasurePureProfileLaw` is a single
`ProbabilityMeasure` on complete pure profiles. The latter is a joint law and
may correlate players. It is not called an independent mixed profile.
Playerwise independence requires a separately constructed product law and is
not inferred from its marginals.

## Semantics

The primitive semantic operation is measurable pushforward:

1. a caller supplies a measurable evaluator from complete pure profiles to an
   outcome;
2. `outcomeLaw` maps the joint profile law through that evaluator; and
3. `pathLaw` is the specialization whose outcome is a complete legal play.

This keeps execution honest. A concrete EFG executor must prove that its map
from a pure profile to a complete path is measurable. No measurable structure
on dependent function spaces, evaluation map, infinite product, or
regular-conditional distribution is synthesized automatically.

## Discrete compatibility

A pure profile embeds as a Dirac probability measure. A `PMF` on complete
pure profiles embeds through `PMF.toMeasure`. Pushforward of the latter is
proved equal to `PMF.toMeasure` of the existing PMF pushforward, so the
compatibility claim is equality of full outcome laws, not merely equality of
expectations or terminal marginals.

Existing `MixedProfile` remains a finite-player family of independent PMFs.
Its `pureProfileLaw` first constructs the independent joint PMF; that joint
law can then use the general `ofPMF` embedding. The new carrier also admits
joint correlated laws that cannot be represented by playerwise independent
mixing.

## Behavioral realization boundary

No unrestricted mixed-to-behavioral equivalence is asserted. Such a theorem
would additionally need:

- measurable evaluation on the relevant dependent strategy spaces;
- a standard-Borel or otherwise disintegrable model;
- a precise independence convention;
- perfect recall/no absent-mindedness;
- regular conditional probabilities, including a version policy at null
  information sets; and
- a proof that the resulting behavioral kernels preserve the requested
  complete path law.

The finite PMF Kuhn theorem remains the implemented equivalence theorem. The
infinite/arbitrary-measure route is recorded as a staged proof plan rather
than an axiom.

## Facade

The reusable carrier lives in `Observed.MeasureStrategy` and is exported only
through `Interface.Equilibrium.Analytic`. It is intentionally absent from the
discrete equilibrium facade and the root aggregate.
