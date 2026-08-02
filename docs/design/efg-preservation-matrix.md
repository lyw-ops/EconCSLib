# EFG Preservation Matrix

This note is the common vocabulary for claims made by EFG relations,
realizations, serializers, and compilers. Lean declarations remain
authoritative. A cell marked “premise” means the property is not part of the
relation itself: a transfer theorem must receive an explicit certificate.

## Strength vocabulary

- **Hom**: forward structure map and commuting transition diagram; it need not
  be injective or surjective.
- **Iso**: bijective data and strict commuting diagrams. Endpoint-forgetting,
  macro-step compression, reordered simultaneous moves, and administrative
  stuttering are not strict isomorphisms.
- **InformationRefinement**: same strategic dynamics with a directional map
  from finer to coarser information. Strategy lifting and equilibrium transfer
  are directional.
- **Simulation / Bisimulation**: one-way / two-way step matching. Neither name
  alone asserts equality of probability laws.
- **WeakSimulation / WeakBisimulation**: visible steps may correspond to
  multiple administrative steps. These are the standard relations for
  stuttering and serialization.
- **Realization**: a strategy map whose induced semantic law is preserved
  against the stated opponent class. It is not a raw strategy-space
  isomorphism.
- **Coupling**: a joint law supported on a relation. Equality of pushforward
  laws follows only when the relation/function hypotheses say so.

## Measure vocabulary

These four levels are deliberately different:

1. an arbitrary `Measure` has no normalization or legality guarantee;
2. a probability measure additionally has an `IsProbabilityMeasure`
   certificate;
3. a lawful complete-path probability is a
   `ControlledObservedGame.CompletePathLawSemantics`, whose `pathLaw` is
   normalized and is almost surely supported on
   `Arena.IsCompletePlayPathFrom`;
4. an execution-coherent lawful probability additionally satisfies
   `RealizesExecution` or a caller-supplied `ExecutionCoherent` predicate.

The maximum path-law carrier is payoff-free and stores no local kernel, PMF,
countability assumption, strategic-mode tag, or chance-semantics tag.
Discrete PMF and analytic-kernel execution enter through downstream adapters.

## Relation-level matrix

| Relation/certificate | Histories/endpoints | Actions | Information | Chance | Complete path/history law | Objectives | Unilateral deviations | Recall | Roots/subgames | Termination |
|---|---|---|---|---|---|---|---|---|---|---|
| `ControlledObservedGame.Hom` | forward strict history map | dependent information-action map only; no concrete-realization square | private/public/info maps | not included | not included | not included | **not included**: a target may have information states with no source preimage | premise | `MapsRootPresentations` is an extra predicate | premise |
| `ControlledObservedGame.Iso` | bijective complete histories | dependent equivalences with concrete-realization square | private/public/info equivalences | not included | structural path equivalence only; stochastic/path-law equality needs a separate naturality premise | payoff-free objectives may be transported by their own theorem | pure-strategy equivalence and update square | classic/private/public recall iff | exact root and lawful-subgame transport theorems | structural certificates transport through the arena equivalence |
| `ObservedGame.PayoffCompatibleIso` | underlying strict payoff-free iso | inherited | inherited | separate | no law field | adds only the terminal-payoff commuting square | inherited only from the structural iso | inherited | inherited | inherited |
| `ControlledObservedGame.InformationRefinement` | shared strict controlled dynamics | exact concrete actions | directional fine-to-coarse information map | separate | requires a concrete strategy/law lifting theorem | not included | source pure strategies lift; reverse coverage is extra | not automatic | external | premise |
| strict `Simulation` / `Bisimulation` | related endpoints per step | related actions/policies | presentation-specific premise | kernel relation required | only when an execution/coupling theorem is supplied | relation-respecting objective premise | deviation completeness is extra | not automatic | external | not automatic |
| `WeakSimulation` / `WeakBisimulation` | visible histories may skip/stutter | macro action versus micro trace | serialization invariant | kernel coupling | visible trajectory law through the stated projection | projection-respecting objective premise | explicit policy/deviation compilation | explicit theorem only | macro-root map, not strict root identity | requires progress/no-divergence certificate |
| same-game `CompleteHistoryLawRealization` | same occurrence-sensitive history carrier | semantic, through induced histories | arbitrary playerwise strategy carriers | supplied by the concrete semantics, not tagged in the relation | exact bounded complete-history PMF | downstream only through explicit interpretations | source deviations map via the playerwise map; target coverage and strategy isomorphism are separate | not included | not included | bounded fuel only |
| cross-game `CrossGameBoundedCompleteHistoryLawRealization` | explicit source-to-target history map | semantic | arbitrary playerwise strategy carriers | supplied by each concrete semantics | exact PMF pushforward at every profile/current history/fuel | downstream only through explicit interpretations | source update square proved; target coverage is not stored | not included | current history maps explicitly | bounded fuel only |
| same-game `CompletePathLawRealization` | identity history/path carrier | semantic | arbitrary playerwise strategy carriers | supplied by each lawful semantic model | exact whole lawful path-probability equality | measurable pushforwards follow | source update square proved; target coverage and strategy isomorphism are separate | not included | every current history, with no stored root selection | a.s. termination is a separate law property |
| cross-game `CrossGameCompletePathLawRealization` | explicit measurable history and coordinatewise path maps | semantic | arbitrary playerwise strategy carriers | supplied by each lawful semantic model | exact source-law pushforward to target law | measurable pushforwards follow | source update square proved; target coverage and cross-game strategy isomorphism are separate | not included | target current history is the image of the source history | a.s. termination transfer needs an event theorem |
| `PathLawCoupling` | paired path carriers related almost surely | encoded in support relation | not included | joint law supplied explicitly | source, target, and joint are certified probability measures; both marginals are exact | relation-respecting observer requires a theorem | not implied | not implied | not implied | not implied |
| `StrictCompilerPreservation` | strict payoff-free history iso | inherited from strict iso | inherited from strict iso | not included | **not included** | not included | not included | not included | exact chosen-root correspondence | only what the structural iso transports |
| `WeakCompilerPreservation` | weak source/target state relation with nonempty target progress | macro action versus micro trace | not included | not included | **not included** | not included | not included | not included | related initial states only | progress is stored; no-divergence/law preservation is extra |
| payoff-free `FiniteEFGHypotheses.toFiniteHistoryGame` / `toFiniteObservedGame` | `historyEquiv` and `toOriginalIso` preserve occurrence-sensitive complete histories; merged endpoints remain distinct | strict dependent equivalence | private/public/info pullback presentation | `pullDiscreteChanceKernel_eq` | `mapBehavioralHistoryLaw` proves exact bounded complete-history PMF pushforward | terminal/path objectives pull back without endpoint quotienting | pure/behavioral strategy equivalences and update squares are proved | `perfectRecall_iff`, `signalPerfectRecall_iff`, `publicPerfectRecall_iff` | `toOriginalIso_preservesRootPresentation`; `pullSubgameSystem_isLawful` | `toFiniteHistoryGame_hasLengthBound` |

## Declaration anchors

The matrix rows above are backed by the following Lean owners:

- `Observed/ControlledMorphism/Core.lean`: payoff-free `Hom`, strict `Iso`,
  `InformationRefinement`, root-presentation correspondence, structural
  strategy transport, and Iso algebra.
- `Observed/ControlledMorphism/Subgame.lean` and
  `Observed/ControlledMorphism/Recall.lean`: lawful-subgame transport and
  recall equivalences respectively. `Observed/ControlledMorphism.lean` is the
  import-only compatibility aggregate for all three leaves.
- `Observed/ControlledMorphismCompat.lean`: the orthogonal
  `ObservedGame.PayoffCompatibleIso` and legacy payoff-aware adapters.
- `Observed/ControlledDiscreteLaw.lean`: discrete chance presentation,
  payoff-free bounded complete-history semantic realizations, behavioral PMFs,
  and strict stochastic naturality.
- `Observed/ControlledLaw.lean`: the normalized, almost-surely lawful common
  path carrier; measurable history/outcome/payoff interpretations; distinct
  arbitrary-integral and expected-utility theorems; execution coherence;
  same-game and cross-game realizations; identity/strict-Iso bridges; target
  deviation coverage; and strategy-space isomorphisms.
- `Observed/ControlledDiscretePathLaw.lean` and
  `Observed/ControlledAnalyticLaw.lean`: the actual discrete behavioral and
  analytic-kernel adapters into that common carrier.
- `Observed/FiniteUnfolding.lean`: compiler-specific occurrence-unfolding
  certificates, including `boundedHistoryLawPreservation`, a concrete
  cross-representation exact behavioral history-law package.
- `Relations/Preservation.lean`: formal aliases for strict/weak relations,
  same/cross-game law realizations and probability couplings, plus compiler
  packages whose constructors prevent a weak serializer from being labelled
  a strict isomorphism.

## Compiler claims

| Frontend/route | Correct preservation description |
|---|---|
| `GameTreeOccurrenceObserved` | Occurrence-sensitive finite tree compiler; may use strict observed structure where its history map is genuinely bijective. |
| legacy `GameTreeObserved` | Endpoint-observed compatibility compiler. It can forget occurrence distinctions and must not be advertised as a strict history isomorphism. |
| `StochasticGameTreeObserved` | Occurrence-sensitive chance compiler with exact local PMF laws; global law claims use the chance execution theorems. |
| `FiniteImperfectObserved` | Finite imperfect-information presentation compiler; information and root claims are those stated by its explicit certificates. |
| FOSG sequentialization | Weak serialization: one simultaneous macro-step is represented by an ordered micro-trace. Different orders are not strict history isomorphisms; macro-root preservation uses the serialization certificate's explicit external `targetRoots` presentation. |
| measurable presentation bridges | Preserve the supplied measurable path law through their explicit kernel/presentation maps; they do not turn PMF strategies into non-atomic general strategies. |

## Review rule

A compiler or transfer theorem should cite the strongest row it actually
constructs. Stronger downstream consequences must be derived through a named
bridge—history/path law to outcome law, outcome law to payoff law, or payoff
law to utility—not asserted by prose. Root visibility, lawful subgames,
deviation coverage, recall, and termination are independent axes unless the
declaration explicitly includes them.
