# Extensive Games — Architecture and Public API

This note is the entry point for EconCSLib's extensive-game architecture. The
library deliberately supports two interoperating representations:

- finite inductive `GameTree`s for structural recursion, backward induction,
  global structural endpoint-policy optimality, and Zermelo determinacy;
- history-indexed Arena/observed EFGs for chance, imperfect information,
  behavioral and mixed strategies, representation transfer, and FOSG
  serialization.

The simulation-oriented stack has granular, build-enforced finite/PMF,
measure-valued infinite-discrete, and analytic entries. Finite clients use
`Interface.Execution.Finite`, `Interface.Relations.Discrete`,
`Interface.Equilibrium.Discrete`, and `Interface.Compilation.Discrete`;
infinite PMF-path clients use `Interface.Execution.Infinite`; analytic clients
use `Interface.Execution.Analytic`, `Interface.Equilibrium.Analytic`, and
`Interface.Restart`. The former `Execution.Discrete`, `Relations`,
`Equilibrium`, and `Compilation` paths remain broad supported aggregates, and
`Interface.SimulationFramework` remains the compatibility import for the
complete stack. The stability policy is specified in
[`efg-public-api.md`](efg-public-api.md), the measured dependency audit and
actual facade DAG in
[`efg-import-granularity.md`](efg-import-granularity.md), and source-level
changes in [`efg-api-migration.md`](efg-api-migration.md).  The authoritative
lifecycle, frontend, historical, root-aggregate, and placement rules are in
[`efg-governance.md`](efg-governance.md); the complete source-based module
register is [`efg-module-status.md`](efg-module-status.md). Detailed
signatures, minimal assumptions, and the full theorem inventory continue in
[`extensive_game-2-reference.md`](extensive_game-2-reference.md).
The audited smart constructors for common observed-game presentations,
including their deliberately unsafe semantic boundaries, are listed in
[`observed-game-constructors.md`](observed-game-constructors.md).
The finite-representation matrix and canonical routes through
`ObservedChanceGame` are audited in
[`efg-representation-compilation.md`](efg-representation-compilation.md).

Part of the [design documentation set](README.md). The implementation and
[`../research/efg_simulation_framework_status.md`](../research/efg_simulation_framework_status.md)
are authoritative when a research note describes an older boundary.

## 1. Design principles

### Use the strongest valid representation relation

The framework distinguishes relations instead of calling every compiler an
isomorphism:

| Relation | Required preservation | Typical use |
|----------|-----------------------|-------------|
| Strict observed-EFG isomorphism | bijective histories/actions; exact observations, public states, information, payoffs, chance laws, and presentation-designated continuation roots; lawful subgame systems transport separately | state/action relabeling or genuinely equivalent EFG encodings on one player carrier |
| Information refinement | strict dynamics plus directional forgetting/lifting of information | fine versus coarse information models |
| Kernel simulation/bisimulation | related stochastic steps with exact PMF couplings | non-functional stochastic representation changes |
| Weak/stuttering simulation | one macro step matched by a positive finite micro execution | FOSG sequentialization with administrative states |

Consequently, inserting hidden player/chance states is not presented as a
strict history-tree isomorphism. Exactness is instead proved at macro
boundaries for traces, payoff laws, unilateral deviations, Nash equilibrium,
and Nash on caller-declared finite-horizon macro continuations.
Bijective player-label changes use `ControlledObservedGame.relabelPlayers`
before applying same-carrier relations; this preserves lawful subgames and
dependent pure profiles.

### Keep strategy and solution concepts game-bound

Pure, behavioral, and mixed strategies are indexed by the game whose action
and information types they use. Nash and SPE predicates are stated on the
corresponding game form or continuation family rather than on detached
function types.

### Keep assumptions local

The structures support infinite state spaces. Finiteness, decidable equality,
termination, perfect recall, and order assumptions occur only on the
constructions and theorems that need them.

### Keep the two Kuhn theorems distinct

- `GameTree` structural recursion proves existence of a globally optimal
  endpoint policy. The root-bound occurrence compiler separately proves
  canonical pure SPE existence for a concrete finite perfect-information EFG.
- The observed-EFG Kuhn theorem proves realization equivalence between mixed
  complete plans and behavioral strategies under finite perfect recall.

The second is a realization theorem, not a literal isomorphism of strategy
spaces.

## 2. Module layers

```text
GameTheory/GameForm.lean
  GameForm/{Basic,Law,Continuation,IndexedContinuation}.lean

Math/Probability/PMF.lean
  PMF/{Equiv,FiniteProduct,Coupling,ToMeasure,ConditionalSampling,
       ConditionalProduct,DeferredSampling}.lean

GameTheory/ExtensiveGame/
  Basic → Strategy → Play → Subgame
                      ↓
  Execution/{History,StoppedExecution,StochasticExecution}
                      ↓
  Simulation/{Morphism,KernelArena,MeasurableKernelArena,
              Simulation.Kernel.Execution,Simulation.Kernel.Endpoint,
              Simulation.Kernel.StatePath,Simulation.Kernel.HistoryPath,
              Simulation.Kernel.EventPath,Simulation.Kernel.ObservedEvent,
              Simulation.Kernel.RealizedInformation,
              Simulation.Presentation.Chance.KernelBridge,
              Simulation.Presentation.Chance.Realized,
              KernelTrajectory,
              KernelWeakSimulation}
                      ↓
  Observed/{Game,...,KuhnConditioning,StrategyBridge}

  FOSG/{FOSG,FOSGBehavioralSerialization,
        FOSGSequentialization,FOSGContinuation}

  GameTree → backward induction / structural endpoint optimality / NE / Zermelo
           → Compiler/{GameTreeObserved,
                       GameTreeOccurrenceObserved,
                       StochasticGameTreeObserved,
                       FiniteImperfectObserved}
```

[`Interface/Core.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Interface/Core.lean)
is the common base. The shallow dependency-ordered ladder is
[`Execution/Finite.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Interface/Execution/Finite.lean)
→
[`Relations/Discrete.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Interface/Relations/Discrete.lean)
→
[`Equilibrium/Discrete.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Interface/Equilibrium/Discrete.lean).
[`Execution/Infinite.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Interface/Execution/Infinite.lean)
adds the intrinsically measure-valued infinite discrete path semantics.
Analytic execution extends that stable infinite-discrete facade, and
[`Equilibrium/Analytic.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Interface/Equilibrium/Analytic.lean)
reuses both discrete equilibrium and analytic execution.
[`Restart.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Interface/Restart.lean)
is the analytic restart branch;
[`Compilation/Discrete.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Interface/Compilation/Discrete.lean)
is the measure-free compiler branch. The former `Execution.Discrete`,
`Relations`, `Equilibrium`, and `Compilation` files retain their old broad
closures as compatibility aggregates. Import the smallest applicable facade;
[`SimulationFramework.lean`](../../EconCSLib/GameTheory/ExtensiveGame/Interface/SimulationFramework.lean)
is retained as a compatibility-only complete-stack aggregate.
[`GameForm.lean`](../../EconCSLib/GameTheory/GameForm.lean) aggregates the
representation-neutral semantic layer.

## 3. Finite `GameTree` track

`GameTree` is an inductive, structurally finite, perfect-information,
no-chance representation. Its main theorem path is:

```text
GameTree.size
  → strong induction
  → backward-induction value and optimal strategy
  → global structural endpoint-policy optimality
  → root Nash equilibrium
  → zero-sum Zermelo specialization
```

Backward-induction comparison uses `[TotalPreorder U] [DecidableLE U]`;
arithmetic enters only in the zero-sum specialization. The detailed API,
including minimal assumptions for every declaration, is documented in
[`extensive_game-2-reference.md`](extensive_game-2-reference.md).

## 4. Observed-EFG track

An `ObservedGame` assigns semantics to complete typed histories:

- private observations for every player;
- a public state and private-to-public compatibility;
- decision information states and information-indexed abstract actions;
- terminal payoff vectors;
- an explicit predicate of presentation-designated continuation roots.

Common history-information models should prefer the orthogonal constructors
documented in
[`observed-game-constructors.md`](observed-game-constructors.md):
public projection, presentation-designated roots, lawful subgame systems, and
chance laws remain separate arguments rather than hidden defaults.

The designated predicate alone is not a standard-subgame certificate.
`ObservedGame.IsLawfulSubgameRoot` treats the initial history as the whole
game by convention and states proper-root singleton plus information-set
closure conditions independently of designation.
`ObservedGame.SubgameSystem` selects a nonempty, possibly conservative system
of such roots independently of presentation metadata, while
`CompleteSubgameSystem` proves that every structurally lawful root is selected.
`CompleteSubgameSystem.canonical` exists for every observed game.
`SubgameSystem.IsPresentationVisible` separately records when all selected
roots are also presentation-designated.

`ObservedGame.Iso` preserves this structure strictly. `ObservedChanceGame.Iso`
adds exact chance-kernel pushforward. The induced pure, behavioral, and mixed
continuation semantics preserve complete bounded history and payoff PMFs and
transfer Nash on presentation-designated continuations in both directions.
Subgame perfection on an explicit lawful system uses the `...On`
predicates. Complete standard SPE uses a `CompleteSubgameSystem`. Strict
isomorphisms transport both levels and preserve their equilibrium predicates.

For strict-isomorphism transfer of bounded Nash on presentation-designated
continuations, the canonical public entry points are
`ObservedGame.Iso.isPureNashOnRootsAtFuel_iff`,
`ObservedChanceGame.Iso.isBehavioralNashOnRootsAtFuel_iff`,
and
`ObservedChanceGame.Iso.isMixedNashOnRootsAtFuel_iff`.
Each theorem receives the source and target root presentations explicitly.
Equivalent derivations through continuation families and information
refinements remain build-enforced private regressions, not alternate
downstream APIs.

Information refinements retain strict dynamics while changing information
granularity. Their default transfer direction reflects equilibrium from the
finer deviation space; two-way transfer requires explicit strategy or
semantic-deviation coverage.

The executable stochastic layer uses `PMF`. The analytic
`MeasurableKernelArena` layer instead stores a genuine Mathlib Markov kernel
on the dependent state/action bundle and therefore admits non-atomic
successor laws. `KernelArena.toMeasurable` embeds every discrete arena
exactly. `MeasurableKernelArena.ActionPolicy` is a killed action kernel: it is
zero at terminal states and a probability law concentrated on the current
dependent action fiber elsewhere. `ActionPolicy.stepKernel` is formally
Markov and terminal-absorbing. The old `KernelArena.Policy.stepLaw` is
recovered exactly after conversion, without assuming the entire action type
is countable. `Simulation.Kernel.Endpoint` iterates this step, proves the
finite-horizon Chapman--Kolmogorov and Markov properties, and recovers
`KernelArena.stateLawFrom` exactly. `Simulation.Kernel.StatePath` applies Mathlib's
Ionescu--Tulcea construction to the stopped step kernel. Its infinite
discrete-event state-path law is a probability measure; coordinate `n` is
exactly the finite endpoint law at horizon `n`, including exact discrete PMF
recovery. At this point in the dependency chain, measure-valued observed
strategies remain a separate extension boundary; later analytic-presentation
modules supply it. `Simulation.Kernel.HistoryPath` generalizes the policy input to a
time-indexed measurable kernel on complete finite state prefixes. Its
coordinate successor law correctly depends on the full preceding prefix
measure, and every stationary `ActionPolicy` embeds with exactly the same
history-step kernels and whole path law. `Simulation.Kernel.EventPath` retains
each selected action occurrence beside its sampled successor state. Its
event-history policy may inspect complete finite state/action event prefixes;
forgetting recorded actions from an embedded state-history policy recovers
the complete original infinite state-path law exactly.
`Simulation.Kernel.ObservedEvent` factors raw event-prefix dependence through a
fixed measurable information statistic. Policies sharing that statistic are
structurally information-consistent; measurable fine-to-coarse information
maps pull coarse policies back without changing the compiled event executor
or its whole path law. Its concrete action-bundle codomain has an explicit
boundary: equal information at two nonterminal prefixes forces their latest
states to be equal.
`Simulation.Kernel.RealizedInformation` repairs that boundary without weakening
information consistency. A policy chooses only an abstract action law indexed
by information; a fixed, possibly stochastic kernel realizes each abstract
action against the complete concrete event prefix. Equal information forces
the abstract laws to agree, while the compiled concrete bundle laws may
differ when the two history-dependent realization sections differ. The
compiler proves normalization and legality under explicit s-finiteness and
almost-sure realization hypotheses, and information-factor pullback preserves
the raw executor and whole event-path law exactly. The absent-minded
regression proves this policy class is inhabited where the direct
concrete-bundle policy class on the same terminal-tagged information structure
is not.
`Simulation.Presentation.Chance.KernelBridge` lifts complete histories to a deterministic
kernel arena and turns the existing behavioral/chance history policy into a
stationary analytic policy. Player and chance branches are preserved exactly,
and every finite analytic endpoint measure equals `PMF.toMeasure` of the old
stopped-history PMF. Instantiating the realized-information layer for a
general observed-chance game still requires an explicit analytic presentation:
the existing carriers do not themselves provide measurable spaces or the
measurability of the required tagged dependent realization.
`Simulation.Presentation.Chance.Realized` defines that explicit certificate. It
fixes measurable information and realization independently of profiles,
factors player histories through the original `InfoState`, and certifies exact
raw-policy compilation. From the certificate it derives exact abstract
player-information consistency, player/chance concrete branches, complete
joint event and state paths, and all finite stopped-history measures. The
absent-minded example constructs the certificate at every prefix. This is not
an unconditional adapter.
`Simulation.Presentation.Chance.Countable` now supplies the canonical
countable-discrete case. It requires countability only of complete histories
and the total complete-history/local-action carrier. Player tags retain only
information points witnessed by player-controlled histories; their
countability follows as a history image, and their action fibers embed through
the witnessing `actionEquiv`. The ambient player type and unreachable
declared information/action fibers need not be countable. From those
hypotheses it derives countable tagged carriers and event prefixes, installs
discrete measurable structures, and builds a fixed terminal/player/chance
realization. For every behavioral profile it proves that measure bind
recovers the original player/chance PMF action law exactly, hence produces an
`AnalyticPresentation` without a model-specific compilation proof. The
absent-minded regression needs only a finite complete-history cover. A strict
sparse-player regression uses the uncountable type `Unit ⊕ ℝ`; every unused
real-indexed player has uncountable `ℝ` information and action fibers, yet the
automatic presentation and exact compilation theorem still apply because
those points are unreachable. The analytic presentation and noncomputable
PMF-policy embedding split terminality classically, so neither API requires a
terminal-decidability instance. Only comparison with the old executable
bounded stopped-PMF evaluator retains that evaluator's decidability premise.
`Simulation.Presentation.Chance.MeasurableHistory` and
`Simulation.Presentation.Chance.Measurable` cross the reachable-countability
boundary without pretending that arbitrary carriers are measurable. A
`MeasurableHistoryModel` explicitly supplies measurable structures on
complete histories and their dependent legal-action bundle, measurable
projection and history append, measurable terminality and singletons, and an
exact deterministic append transition kernel. A `MeasurablePresentation`
then supplies measurable information, profile-independent realization, one
measurable realized policy for every admitted behavioral profile, and exact
local player/chance kernel equations. Those local equations generate the
joint event and state path laws without a second global compilation axiom.
Every old `AnalyticPresentation`, including the canonical countable one,
lifts exactly through `toMeasurablePresentation`.

The strict uncountable regression has one real action at the root. Its
complete histories are measurably equivalent to `Unit ⊕ ℝ`, its legal bundle
to Borel `ℝ`, and both carriers are proved non-countable. Every behavioral
`PMF ℝ` compiles exactly through a measurable deterministic realization.
This is an uncountable reachable presentation.

`Simulation.Presentation.Kernel.Core` crosses the remaining action-law
boundary. The measurable history model now depends only on the structural
`ObservedGame`, not on an attached PMF chance law. A
`MeasurableKernelPresentation` fixes information, realization, and a
measurable concrete chance-action kernel. Each `KernelBehavioralProfile`
supplies an information-indexed abstract Markov kernel and proves exact
agreement with the fixed chance law at chance prefixes. Information
consistency and unilateral-deviation agreement are stated at the abstract
kernel level; chance equality is stated after realization, where it remains
valid even for non-injective realizations.

Every old `MeasurablePresentation` embeds exactly, and the canonical
countable constructor exposes the same adapter without duplicating its
executor. The strict regression uses unit-interval volume, proves the
compiled player and genuinely chance-controlled bundle laws are the same
non-atomic pushforward, and proves neither law is `PMF.toMeasure` of any PMF.
For uncountable information spaces, construction of a measurable profile
remains an explicit certificate obligation.

`Simulation.Presentation.Kernel.ProfileAssembly` constructs joint profiles from one
jointly measurable tagged player kernel, explicit measurable role
certificates, and a fixed abstract lift of chance. Unilateral replacement is
measurable singleton branching; splitting and reassembling any admitted
profile preserves its compiled event policy exactly.
`Simulation.Equilibrium.Outcome` keeps economic evaluation separate from
execution. A `PathUtility` is explicitly measurable and its expected utility
requires an integrability certificate; `BoundedPathUtility` supplies that
certificate for every admitted profile. Constructive Nash quantifies over
the certified `PlayerStrategy` deviations of a profile assembly. Terminal
payoffs enter through a measurable extension. `TerminatesBy` gives the safe
fixed-horizon bridge; `TerminatesAlmostSurely` instead requires eventual
terminal absorption and supports an explicit zero-guarded eventual payoff.
For bounded terminal payoff, stopped utility converges almost everywhere and
in expectation by dominated convergence. Thus no endpoint payoff is silently
read on a nonterminating path. The one-step payoff regression proves a
certified deviation changes the time-one state law, raises expected stopped
payoff from zero to one, and refutes Nash for the baseline profile. A second
fair repeat-or-stop regression proves unfinished mass is exactly `2⁻ⁿ`,
almost-sure terminal absorption holds, and every fixed `TerminatesBy`
certificate fails.

`Simulation.Continuation.Path` starts an Ionescu--Tulcea trajectory at an
arbitrary absolute event time and a supplied complete joint event prefix. Its
tail-indexed event and state laws have the prefix's latest event at coordinate
zero, while every later policy query still receives the original clock and
prefix. `Simulation.Continuation.Observed` canonically encodes a dependent
base history as such a prefix: coordinate zero is the empty history and every
successor coordinate records the concrete incoming action occurrence. The
encoding preserves all earlier coordinates, ends at the supplied complete
history, and uses the history length as absolute event time.

On that constructive absolute-prefix law, the observed layer defines
continuation expected utility, root-predicate Nash, and unqualified
measurable-kernel subgame perfection for bounded path utility. It also lifts
almost-sure absorption, baseline-and-deviation termination certificates,
expected eventual terminal payoff, and terminal-payoff subgame perfection.
At the empty root, the continuation state law and expected bounded utility
are exactly the existing time-zero laws. These predicates retain the jointly
measurable player profile rather than replacing it with an arbitrary product
of player strategies.

The old arbitrary-root law remains available under explicit **fresh-clock
restart** names. That qualifier is semantically necessary: information
carriers, abstract action carriers, realization kernels, and player kernels
may all depend on the event-time index and event prefix. The strict clock
boundary regression proves that a fresh restart and absolute-prefix
continuation from the same latest state can have different next recorded
actions and hence different future event-path measures. No theorem identifies
the fresh-clock law with a regular conditional distribution.

`Simulation.Continuation.Conditioning` gives the precise conditional-law
bridge for absolute-prefix continuation. Under a standard-Borel assumption on
the shifted future event-path space, the joint prefix/future law factors
exactly through the constructive continuation kernel, so a regular conditional
kernel agrees with it almost everywhere under the prefix marginal. A
measurable singleton of nonzero prefix mass upgrades that equality to the
specific history and yields the normalized joint-mass formula. At zero mass,
the formula cannot equal the constructive probability law even on the
universal future event. The observed lift transports the positive-atom result
to canonical event paths, state paths, and bounded expected utility. It makes
no pointwise regular-conditional claim at null histories, where versions are
not probabilistically identified.

The solution-concept refinement is strict. The finite deterministic
`MeasurableKernelContinuationNashBoundary` regression constructs a one-player
profile that earns the uniform payoff bound at the initial history and is
therefore Nash there against every admitted measurable deviation. Its second
decision history has probability zero under that baseline, but the canonical
absolute-prefix continuation retains the root action occurrence and absolute
time. At that subgame, one certified replacement changes expected payoff from
zero to one. The same baseline is thus initial-root Nash and not
measurable-kernel subgame perfect.

`ObservedMeasurableKernelRestartCompatibility` provides the exact semantic
boundary between the two constructive executors. A raw full-event comparison
would be structurally wrong at a nonempty root: absolute continuation tail
coordinate zero retains the action occurrence entering the root, while a
fresh restart uses the distinguished initial marker. The normalized event
law erases only that marker difference and leaves every later event intact.
Equality of normalized event laws implies equality of state-path laws.
Conversely, state-law compatibility is characterized exactly by equality of
all initial finite state-prefix marginals, using uniqueness of projective
limits. For bounded utility, fresh and absolute rootwise Nash—and hence Nash
on every presentation-designated continuation—are equivalent when the baseline and every certified
unilateral deviation satisfy state-law compatibility. The clock-dependent
regression remains unequal after event normalization, so the compatibility
premise is not vacuous.

The same module supplies the measurable splice used by the local
criterion. `spliceContinuationPath` preserves every event through the
absolute continuation time and uses fresh coordinates `1, 2, ...` at later
absolute times. The resulting spliced law has the supplied absolute prefix
as an exact Dirac marginal. After tail shifting and normalizing only the root
occurrence marker, it is exactly the original fresh event-path law. Therefore
an equality between the actual absolute trajectory and the spliced
trajectory implies normalized event compatibility, state compatibility, and
the existing payoff/equilibrium transfers. That trajectory equality is also
equivalent to equality of all complete initial finite-prefix marginals.

`IsFreshRestartPartialStepCompatibleAt` proves those marginals recursively.
At every future offset, it requires the next spliced-fresh finite-prefix law
to equal the current spliced law advanced by the actual absolute one-step
`partialTraj` kernel. The condition is distributional rather than pointwise:
it permits kernels to differ on null or unreachable prefixes. Finite splice
measurability and the exact fresh-partial-trajectory representation make the
successor induction explicit. The resulting profile and assembly lifts imply
normalized event/state compatibility and bounded-utility designated-root Nash, subgame-perfection-on, and complete standard-SPE equivalence
when the condition holds for the baseline and every certified deviation. The
strict clock-dependent regression proves that the local condition is not
automatic.

For a more directly checkable sufficient condition,
`IsFreshRestartStepKernelCompatibleAt` compares the two one-step extension
kernels before integration. At each offset it requires equality almost
everywhere under the generated fresh finite-prefix law between:

1. fresh-clock one-step extension followed by finite splicing; and
2. finite splicing followed by the actual absolute-clock one-step extension.

`Measure.comp_congr`, kernel-map composition, and the fresh partial-trajectory
recursion turn this generated-law almost-everywhere equality into the exact
distributional recurrence above. A pointwise strengthening is also exposed
for structural policies. The observed-profile and deviation-complete
assembly lifts yield the same bounded-utility designated-root Nash, subgame-perfection-on, and complete standard-SPE equivalences. No
measurable-singleton, countability, positive-reachability, or equality on
generated-null prefixes is introduced.

The global pointwise strengthening is sometimes unnecessarily strong because
it also checks finite-prefix functions with a noncanonical coordinate-zero
event. `IsFreshRestartRootedStepKernelCompatibleAt` restricts the structural
premise to fixed points of canonical coordinate-zero replacement. In a fully
general measurable space this fixed-point set need not be measurable, so the
library does not claim it has full measure. Instead,
`freshRestartFinitePrefixMeasure_map_setInitialPrefix` proves reset
invariance, and `measureComp_eq_of_map_eq_self_of_forall` integrates kernel
equality after the reset. This proves the rooted condition implies the exact
distributional recurrence without measurable singletons or a measurable
diagonal. Profile, deviation-complete assembly, Nash, and SPE lifts are
provided directly.

The same rooted certificate is exposed at the primitive event-kernel layer
as `IsFreshRestartRootedPathStepKernelCompatibleAt`. It requires equality of
the absolute-clock and fresh-clock `pathStepKernel` measures at each matching
rooted prefix. This comparison includes terminal absorption, the behavioral
action kernel, and the recorded arena transition; equality of action kernels
alone is not substituted for equality of next-event laws.
`partialTraj_succ_apply_eq_map_appendContinuationEvent` identifies a
successor partial trajectory with the next-event law mapped by deterministic
prefix extension, while finite splicing commutes with that extension.
Conversely, mapping rooted one-step prefix equality to the newest coordinate
recovers the primitive event-kernel equality. Thus the two rooted
certificates are formally equivalent and have identical assembly and
designated-root Nash, subgame-perfection-on, and complete standard-SPE consequences. The clock regression proves primitive failure
directly at fresh offset zero.

The lowest current structural interface is
`IsFreshRestartRootedActionKernelCompatibleAt`. At each rooted fresh prefix
it compares `EventHistoryActionPolicy.kernel` at fresh time `offset` with the
same policy at absolute time `start + offset` on the spliced prefix.
`latestEventState_spliceContinuationPrefix_eq_of_rooted` proves that these
prefixes have the same latest state. Terminal action measures are therefore
both zero. On a nonterminal prefix, equal action measures bind through the
same `recordedTransition` and give equal primitive event-step laws.

The converse is also formal, and depends essentially on the event-path
design: mapping a nonterminal recorded event to `PathEvent.action` recovers
the behavioral action law mapped by `Sum.inr`. Since `Sum.inr` is a
measurable embedding, its pushforward on measures is injective. Hence rooted
action-kernel, primitive event-step, and successor-prefix compatibility are
equivalent. This is not a claim that the policy is globally stationary or
prefix-insensitive; only matching rooted fresh/spliced prefixes are
compared. Deviation-complete assembly and designated-root Nash, subgame-perfection-on, and complete standard-SPE lifts are provided, and
the clock regression separates the action laws directly at offset zero.

For policies intended to satisfy the same structural law at every
continuation, `IsFreshRestartRootedActionKernelCompatible` quantifies the
root-scoped action condition over all retained starts and finite prefixes.
This root-uniform proposition is stronger than compatibility at a selected
root and is not inferred for arbitrary history-dependent policies. Its
observed-profile wrapper instantiates the property at every canonical
continuation root. The deviation-complete assembly wrapper requires the
property for the baseline and every admitted unilateral deviation, then
supplies any selected-root predicate and the SPE root set. The strict clock
policy fails the global certificate through its existing offset-zero
separation.

`EventHistoryStatistic` provides a reusable sufficient construction for the
global certificate. Its measurable value type is fixed across event times,
so the statistic at fresh time `offset` can be compared directly with its
value at absolute time `start + offset`. A raw policy
`FactorsThroughStatistic` when its action measure is one common measurable
kernel evaluated at that statistic. Factorization plus equality of the
resulting action measures on rooted fresh/spliced pairs implies root-uniform
action compatibility; literal statistic-value invariance implies this
weaker behavioral premise. The statistic embeds into the existing
`EventInformation` hierarchy, and the induced information policy recompiles
to the original raw policy exactly. The canonical latest-state statistic is
invariant, which supplies the result for every stationary state-Markov
policy. The richer clock-and-latest-state statistic is not literally
invariant, but a clock-ignoring action law remains invariant and proves the
same certificate. This interface is sufficient rather than necessary;
compatibility is not claimed to force factorization through a chosen
statistic.

For information spaces that genuinely change with the clock,
`EventInformation.FreshRestartRebase` transports
`Information (start + offset)` to `Information offset`. The map may depend on
the retained complete prefix, is measurable for each fixed root and offset,
and is not required to be an equivalence. Its rooted-splice law states that
represented absolute information transports to represented fresh
information. If an `EventInformation.ActionPolicy` is globally natural along
that rebase, its compiled raw policy is root-uniform action compatible.
Existence of the transport and kernel naturality are separate premises. A
`Fin (time + 1)` example proves the interface supports genuinely different
information types and formally separates a natural stationary policy from a
clock-sensitive nonnatural one.

### Restart-compatibility API navigation

`ObservedMeasurableKernelRestartCompatibility` remains the compatibility
aggregate for every existing restart declaration. The stable facade is
`Interface.Restart`; its implementation is ordered by the actual proof
dependency:

```text
Core → Trajectory → Certificates → Observed → Assembly → Equilibrium
```

Use the shortest route matching the fact already available:

```text
I already have state-law compatibility
  → use the canonical compatibility transfer

I can prove generated-law a.e. step equality
  → convert to partial-step/state compatibility

My strategy is a structural rooted action policy
  → use the rooted action certificate

My strategy is built through a statistic or time-varying information
  → use the factorization/rebase constructor
```

The canonical semantic entries are
`KernelBehavioralProfile.IsFreshRestartStateCompatibleAt`,
`ProfileAssembly.FreshRestartDeviationCompatibleAt`/`On`, and the
`BoundedPathUtility` designated-root Nash, subgame-perfection-on, and complete standard-SPE theorems ending in `_of_compatible`.
Generated-law almost-everywhere step compatibility and rooted behavioral
action-kernel compatibility are the two recommended direct certificates;
statistic factorization and information rebase are the recommended structural
constructors. Splicing, full finite-prefix equality, partial-step recurrence,
rooted prefix/path steps, and global pointwise strengthenings remain
transitively name-resolvable experimental proof tools, not separately frozen
public API.

The navigation distinction does not weaken the following boundaries:

- fresh-clock restart is not automatically absolute-prefix continuation;
- constructive continuation is not automatically a pointwise conditional law
  at null histories;
- equality of transition laws does not imply equality of recorded action
  laws;
- a compatible policy need not factor through a chosen statistic;
- existence of an information rebase does not imply policy naturality;
- Nash at the initial root does not imply SPE.

## 5. Perfect recall and finite Kuhn realization

Perfect recall records each player's ordered prior information/action history.
For finite decision-information types:

1. independently sampling one complete behavioral action table realizes
   behavioral execution exactly;
2. conditioning an arbitrary mixed plan on continuation-relative personal
   decisions constructs a root-scoped behavioral realization;
3. complete bounded history and payoff laws agree exactly;
4. arbitrary unilateral deviations have exact rootwise semantic realizations.

Therefore `isBehavioralNashOnRootsAtFuel_iff_mixed` proves two-way bounded
SPE equivalence between a behavioral profile and its independently sampled
complete-plan profile on the explicitly supplied roots. The
mixed-to-behavioral map remains root-scoped because
one root-independent map for every arbitrary correlated mixed plan would be
false in general.

## 6. FOSG serialization

The FOSG layer keeps simultaneous joint actions as the compact macro
presentation. Its finite-player serializer expands a macro action into hidden
turn-taking decisions and a chance transition. This changes micro histories,
so the structural bridge is a progressing weak/stuttering simulation.

Nevertheless, relation-supported PMF couplings prove exact macro endpoint,
trace, and payoff laws. Behavioral strategies, unilateral deviations, Nash
equilibrium, and Nash transfer on caller-declared finite-macro-horizon continuations in both directions.

## 7. Verification and remaining boundary

Stable Lean modules contain no ordinary `sorry` or `admit`. Changes to this
stack should run:

```bash
lake build
lake build EconCSLib.Examples
python3 scripts/check_lean_placeholders.py EconCSLib
git diff --check
```

The generic discrete event-time infinite path and terminal-payoff convergence
layer is implemented in `Execution/InfiniteTrajectory.lean`. Non-atomic
one-step transition laws are representable in
`Simulation/Kernel/Arena.lean`; terminal-aware normalized one-step
execution is implemented in `Simulation/Kernel/Execution.lean`, and
finite endpoint iteration in `Simulation/Kernel/Endpoint.lean`.
Infinite discrete-event analytic state paths and their exact endpoint
marginals are implemented in `Simulation/Kernel/StatePath.lean`.
Finite-state-prefix-dependent policies and their exact stationary
specialization are implemented in
`Simulation/Kernel/HistoryPath.lean`.
Joint state/action event paths, event-prefix-dependent policies, and exact
state-path recovery are implemented in
`Simulation/Kernel/EventPath.lean`.
Fixed measurable event-information structures, information-indexed policies,
and exact fine-to-coarse pullback are implemented in
`Simulation/Kernel/ObservedEvent.lean`.
Abstract information-action kernels, fixed history-dependent stochastic
realization into legal concrete action bundles, and exact execution-preserving
pullback are implemented in
`Simulation/Kernel/RealizedInformation.lean`.
The complete-history analytic lift for `ObservedChanceGame`, exact player and
chance one-step laws, and exact finite stopped-history measure comparison are
implemented in `Simulation/Presentation/Chance/KernelBridge.lean`.
Explicit analytic presentation certificates connecting original player
information to realized abstract policies, with exact joint path and finite
law consequences, are implemented in
`Simulation/Presentation/Chance/Realized.lean`.
Formal reverse regressions show that the raw transition, executed one-step
law, every positive finite endpoint unit-interval volume law, and the
resulting whole path law are not any `PMF.toMeasure`. A generated-state-path
lower-half cylinder is measurable, nonempty, proper, and has probability
exactly one half. A separate
absent-minded regression proves that the current concrete-bundle information
policy cannot merge two distinct nonterminal history states, even when the
behavioral profile correctly reuses one abstract information-action law. A
second absent-minded regression constructs the realized abstract-action
policy on a terminal-tagged information structure, proves its two equal
abstract laws compile to distinct legal concrete laws, and proves the old
direct concrete-bundle policy on that same information structure is
uninhabited. A third regression packages that construction as an actual
observed-chance analytic presentation and proves exact compilation at every
event prefix. A fourth regression obtains the same certificate from the
canonical countable-discrete constructor and again proves equal recurring
abstract laws plus the exact two-step stopped-history law. A fifth regression
proves that the ambient player type and its unreachable declared
information/action carriers may be uncountable; only the reachable history
fragment is counted. A sixth regression uses a genuinely uncountable
reachable real-action history space with explicitly transported measurable
structures and exact local compilation. A seventh reuses that model with
unit-interval volume and proves strict non-PMF player and chance action laws.
Remaining extensions include broader model-specific infinite-horizon
equilibrium applications, model-specific choices of regular conditional
versions at null histories, true continuous-time semantics, further
compiler-specific recall proofs, analytic-to-finite/FOSG continuation SPE
transfer theorems, and a direct finite/well-founded Arena pure-SPE existence
proof. Player-indexed measurable deviations, joint event histories, and both
pointwise rooted and generated-law restart certificates are already part of
the implemented analytic layer.

For theorem names and proof-route rationale, see:

- [`extensive_game-2-reference.md`](extensive_game-2-reference.md);
- [`../research/extensive_game_architecture.md`](../research/extensive_game_architecture.md);
- [`../research/efg_simulation_framework_status.md`](../research/efg_simulation_framework_status.md).
