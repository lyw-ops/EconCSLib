# EFG mathematical provenance

This matrix distinguishes textbook mathematics from EconCSLib
representations and bounded interfaces. A citation supports only the row's
stated hypotheses and conclusion. Exact preservation, compilation, and
restart theorems are generally library-specific even when the objects they
transport are standard.

## Provenance matrix

| Declaration | Source | Source hypotheses | Lean hypotheses | Representation translation | Verification status | Gap |
|---|---|---|---|---|---|---|
| `ControlledDecisionGame`, `InfoState`, `InfoAction`, `infoAt` | [MFoGT §6.3.1] | finite extensive form; information partitions decision nodes with common actions | no finiteness in the carrier; mover equality plus constructive `IsDecision`; local action equivalence at every represented decision occurrence | information classes become an indexed raw carrier and dependent abstract-action fiber over complete histories; observation is not required for strategy semantics | definition implemented | equivalence with every finite partition presentation is not packaged as a general compiler theorem |
| `ControlledObservedGame`, `Observation`, `PublicObservation`, `infoObserve` | source observation models plus EconCSLib factorization | current private/public signals may be defined at every history | observation extends, rather than defines, the minimal decision carrier; decision memory projects to the current private signal | separates all-history signals from acting-player information and permits memory states with the same current observation | definition implemented | source-relative observation fidelity remains compiler-specific |
| `DecisionInfoWitness`, `RepresentedInfo`, `AllDecisionInfoRepresented` | EconCSLib-specific | — | explicit complete history, mover, constructive decision evidence, and `infoAt` equality | replaces informal “node belongs to information set” by occurrence evidence; strategies ignore ghost raw coordinates while full representation remains optional | proved in carrier/infrastructure | no literature claim |
| `PerfectRecall` | [MFoGT Def. 6.3.3]; [Kuhn 1953 §4] | player remembers earlier information and own actions | equality of current information states forces equality of ordered own-decision histories | partition condition is stated directly on complete-history occurrences | implemented | no general equivalence theorem to every textbook tree encoding |
| `RecallCertificate.perfectRecall` and `recallCertificate_nonempty_iff_perfectRecall` | standard definition under an EconCSLib factorization | same recall condition | decidable player equality; the reverse implication uses classical representative choice only inside a proposition | factors the own-decision trace through represented information; executable clients supply certificate data explicitly | both directions proved | certificate is a library API, not a separately sourced theorem |
| `NoAbsentMindedness` hierarchy | [MFoGT Def. 6.3.1, linearity]; recall implication follows the standard hierarchy | an information set is not crossed twice | occurrence-sensitive own-decision traces | repeated decision keys are detected without quotienting histories | implications proved | converse implications are intentionally not claimed |
| `IsLawfulSubgameRoot`, `SubgameSystem`, `CompleteSubgameSystem` | [MFoGT Def. 6.4.2] for the subgame/SPE role | a subgame starts at a singleton information set and does not cut information sets | explicit root occurrence, proper-root information singleton, and continuation information-set closure | roots are complete histories; a complete system selects every structurally lawful root; private/public observation coherence belongs to the ambient `ControlledObservedGame`, not the root predicate | definitions and coverage theorem proved | exact presentation equivalence with every textbook subgame convention is not formalized |
| `IsPureStandardSubgamePerfect` | [MFoGT Def. 6.4.2] | Nash equilibrium in every subgame | no chance, total pure continuation termination, utility interpretation, complete lawful system | standard subgames are occurrence-indexed total continuation game forms | definition and isomorphism preservation proved | no general finite perfect-recall existence theorem |
| `IsPureSubgamePerfectOn` / `IsPureNashOnRoots` | EconCSLib-specific conservative variant | — | selected lawful roots or presentation-designated roots | restricts the quantified continuation family | implemented | must not be cited as standard SPE unless the system is complete |
| `PureTerminatesFrom`, terminal/path objective continuation game forms | EconCSLib-specific totalization | — | explicit per-profile termination from a complete history; objective may depend on terminal occurrence or full history | replaces arbitrary nonterminal payoff fillers with termination-certified operational outcomes | well-definedness and specialization proved | infinite nonterminating utility semantics remains separate |
| `MixedStrategy`, `BehavioralStrategy`, `DiscreteGeneralStrategy` | [MFoGT §6.3.3] | finite extensive form | PMF mixed plans; information-indexed PMF actions; PMF over behavioral strategies | discrete/countably supported carriers are distinguished from arbitrary measures | definitions and embeddings proved | PMFs do not cover non-atomic strategy laws |
| `ArbitraryMeasurePureProfileLaw` | EconCSLib-specific analytic carrier | — | explicit measurable pure-profile model and probability measure | a joint profile law permits correlation; independence is not inferred | pure/PMF embeddings and measurable pushforwards proved | execution realization awaits measurable dependent evaluation/disintegration |
| `FiniteKuhnHypotheses`, `mixedToBehavioral_*` | [Kuhn 1953 §4, Thm. 4]; [MFoGT Thm. 6.3.4] | finite extensive game, perfect recall | finite players/represented decision information where deviation coverage needs it; discrete chance and PMF mixed plans; explicit recall certificate | conditionalization is on own-decision histories at a selected complete root | exact bounded history/payoff laws and Nash transfer proved | theorem is root-scoped and countably supported, not an arbitrary-measure strategy-space isomorphism |
| `countablySupportedMixedToBehavioral_boundedHistoryLaw` | finite-prefix extension of Kuhn's proof, not Kuhn's original theorem | Kuhn's source is finite | arbitrary information-state carrier, PMF mixed plans, recall, every finite fuel | equality is of terminal-aware complete-history PMFs at each bound | proved | infinite path-law equality requires a cylinder/projective-limit bridge |
| `BehavioralProfile.pathLaw` and finite-marginal theorem | supplied probability law with an explicit projective-marginal certificate | caller owns the complete path measure | executable terminal decisions and `FiniteLaw` prefixes; supplied coordinate equalities | event coordinate is a complete terminal-absorbing history | bounded prefixes execute and every claimed marginal equality is explicit | existence/extension of a complete law is not an algorithm and is not inferred from countability |
| `KrepsWilsonConsistencyCertificate` | [Kreps–Wilson 1982, pp. 871–873]; [MFoGT Def. 6.4.5] | finite perfect-recall extensive form; completely mixed perturbations and Bayes beliefs | finite EFG, discrete chance, positive perturbation reach at every represented information coordinate | beliefs are PMFs on `DecisionInfoWitness` indexed by `RepresentedInfo`; convergence is pointwise `Tendsto` in `ℝ≥0∞` | normalization, Bayes formula, and convergence projections proved | canonical conditional continuation-utility evaluator and Nash consequence remain unformalized |
| `IsSequentialEquilibriumFor` | EconCSLib experimental interface informed by Kreps–Wilson | standard source also requires operational sequential rationality | local value evaluator is explicit | packages standard consistency with evaluator-relative rationality | defining projections proved | not yet advertised as standard sequential equilibrium, Nash, or SPE |
| `IsTwoPlayerDetermined` | [MFoGT Def. 6.2.2] | two-player winning game | `Fin 2`, robust pathwise pure strategies | explicit disjunction, separate from totality | definition implemented | none |
| `FiniteTwoPlayerHypotheses.isTwoPlayerDetermined` | [Zermelo 1913]; [MFoGT Cor. 6.2.4] | finite, perfect information, no chance, two-player strict competition | uniform history bound, finite/represented information, no chance, perfect information, total/exclusive winning sets | backward recursion is on complete-history occurrences | proved | classical, noncomputable witness rather than executable solver |
| `WellFoundedTwoPlayerHypotheses.isTwoPlayerDetermined` | standard well-founded extension; delimited from [Gale–Stewart 1953] | source finite theorem does not cover arbitrary infinite branches | well-founded child relation, no chance, perfect information, strategy availability, total/exclusive objective | `WellFounded.fix`; every complete play eventually terminates | proved | no open/closed, Borel, or arbitrary-set infinite determinacy |
| `IsAlmostSurelyWinningUnder` | standard probability-one event terminology | fixed probability law | measurable event under a supplied path measure/policy | randomized winning is evaluated under one executor | monotonicity and support-level implications proved | no two-player stochastic determinacy/value theorem |
| restart splicing and fresh-restart equilibrium APIs | EconCSLib-specific abstraction | — | measurable kernels, explicit continuation/restart clocks, integrability where utilities are used | normalizes event zero and splices accumulated prefixes without changing the represented state path | pointwise, measurability, law, and selected equilibrium results proved | no literature claim that every restart convention is equivalent |
| strict `Iso` and `InformationRefinement` preservation | standard objects under a nonstandard representation; preservation theorems are EconCSLib-specific | source notions are invariant under relabeling/isomorphism | explicit dependent action/history coherence; directionality for refinement | transports complete histories, observations, actions, objectives, recall, subgames, and selected equilibria | matrix of proved equalities/implications exists in `efg-preservation-matrix.md` | refinement reflection requires strategy/deviation coverage and is never inferred automatically |
| finite occurrence unfolding and compiler naturality | EconCSLib-specific representation theorem | — | uniform history bound and locally finite action fibers | compact endpoint states become bounded complete-history occurrences; merging endpoints stay distinct | strict original-history isomorphism and stochastic naturality proved | no claim that arbitrary infinite or measurable presentations compile to a finite carrier |
| `GameTree` occurrence compiler and backward SPE/value theorems | [MFoGT Thm. 6.2.7], [MSZ Thm. 3.13] for finite perfect-information existence; compiler is library-specific | finite perfect-information tree, with/without Nature as stated by each source | inductive finite tree; occurrence compiler; explicit chance variant where used | tree nodes become complete-history occurrences before applying canonical observed APIs | outcome, termination, backward profile, and selected SPE/value theorems proved | do not transfer the source's chance theorem to a no-chance Lean declaration |

## Flagship gaps

The staged nodes
`arbitrary_measure_pure_strategy_realization.md`,
`countably_supported_infinite_kuhn_path_law.md`, and
`sequential_equilibrium_lean_foundation.md` record the exact missing bridges.
They deliberately contain no placeholder Lean theorem.

Additional open scopes remain explicitly outside current theorem claims:

- frontend-wide infinite path-law and complete compiler-preservation packages;
- measurable analytic general-strategy spaces and their evaluation maps;
- Gale--Stewart open/closed and Borel determinacy beyond structural
  well-foundedness.

These scopes belong in focused boundary notes or new staged knowledge nodes
when evidence is ready. They are not maintained in a parallel delivery
roadmap.

## Recurring source labels

- [Kuhn 1953] H. W. Kuhn, “Extensive Games and the Problem of
  Information,” pp. 193--216.
- [Kreps–Wilson 1982] David M. Kreps and Robert Wilson, “Sequential
  Equilibria,” *Econometrica* 50(4), pp. 863--894.
- [Zermelo 1913] Ernst Zermelo, “Über eine Anwendung der Mengenlehre auf die
  Theorie des Schachspiels,” pp. 501--504.
- [Gale–Stewart 1953] David Gale and F. M. Stewart, “Infinite Games with
  Perfect Information,” pp. 245--266.
