# EFG Module Status

This is the source-based lifecycle register for the extensive-form-game
implementation.  It covers every Lean module below
`EconCSLib/GameTheory/ExtensiveGame/`, every module in the representation-neutral
`GameForm` family, and the directly supporting `Math/Probability/PMF` family.
The census was taken from the complete worktree and updated on 2026-08-02; it
contains 183 modules, including 30 modules below
`ExtensiveGame/Simulation/`.

The status describes the role of the module that owns a declaration, not every
declaration made name-resolvable by transitive imports:

- **Canonical** owns the preferred reusable semantics or is a granular stable
  public facade.
- **Frontend** is a supported input or algorithm representation that should
  compile or relate to the canonical layer before acquiring general theory.
- **Historical** is mathematically valid but has different or superseded
  semantics. It is retained and build-checked, but is closed to parallel
  general theory.
- **Compatibility** preserves an established import path. It must remain a thin
  import wrapper and acquire no implementation.
- **Experimental** is opt-in theory whose public contract is not settled.
- **Internal** is proof or compiler implementation reached through a facade;
  its path and helpers are not individually frozen.

| Status | Modules |
|---|---:|
| Canonical | 84 |
| Frontend | 13 |
| Historical | 7 |
| Compatibility | 21 |
| Experimental | 0 |
| Internal | 58 |
| **Total** | **183** |

Recommended-import abbreviations used below are:

| Abbreviation | Full import |
|---|---|
| `GF` | `EconCSLib.GameTheory.GameForm` |
| `PMF` | `EconCSLib.Math.Probability.PMF` |
| `Structural` | `EconCSLib.GameTheory.ExtensiveGame.Interface.StructuralCore` |
| `Core` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Core` |
| `Finite` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Finite` |
| `Infinite` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Infinite` |
| `Analytic` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Analytic` |
| `Relations` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Relations.Discrete` |
| `EqD` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Discrete` |
| `EqA` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Analytic` |
| `Restart` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Restart` |
| `Compile` | `EconCSLib.GameTheory.ExtensiveGame.Interface.Compilation.Discrete` |

Removal-policy codes keep the register readable:

- `C`: only in a major release, with a documented replacement and regression.
- `F`: only in a major release after explicit-frontend migration documentation.
- `H`: only in a major release after a historical-path migration window; never
  invent a false semantic replacement.
- `W`: a compatibility wrapper may be removed only in a major release after
  internal consumers are zero and the replacement has been documented.
- `I`: internal paths may be reorganized behind the stable facade; preserve
  documented public declarations and leave a wrapper when downstream path use
  is known.

## Arena, execution, frontends, and compilers

| Module | Status | Responsibility | Recommended import | Replacement | May grow | Action | Removal policy |
|---|---|---|---|---|---|---|---|
| `EconCSLib.GameTheory.ExtensiveGame.Basic` | Canonical | Minimal `Arena`, payoff-free `ControlledGame`, and state-payoff `ExtensiveGame` compatibility dynamics | `Core` | — | Yes, core only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.Reachability` | Canonical | Finite Arena reachability and game-initial reachability | `Core` | — | Yes, reachability only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.History` | Canonical | Typed finite histories and arena unfolding | `Core` | — | Yes, history only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.CompletePlay` | Canonical | Measure-free history-rooted legal complete plays and terminal absorption | `Core` | — | Yes, structural play only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.DependentFiber` | Internal | Representation-neutral dependent history/action equivalences | `Relations` | facade | Yes, proof helpers only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.Length` | Canonical | Uniform length and `Acc`-based structural well-foundedness certificates | `Core` | — | Yes, structural termination only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.Objective` | Canonical | History-sensitive terminal and complete-path outcomes | `Interface.Objective` | — | Yes, objective only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Winning.Basic` | Canonical | Complete-play winning conditions, prefix decisions, and robust pure winning strategies | `Interface.Objective` | — | Yes, winning-objective semantics only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Winning.Topology` | Canonical | Complete-play agreement cylinders, prefix topology, and measurable prefix objectives | `Interface.Objective` | — | Yes, topological objective boundary only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.StoppedExecution` | Canonical | Terminal-aware deterministic bounded execution | `Core` | — | Yes, execution only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.StochasticExecution` | Canonical | Terminal-aware bounded PMF execution | `Finite` | — | Yes, PMF execution | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.StochasticNaturality` | Canonical | Exact PMF history-execution naturality under strict arena isomorphisms | `Relations` | — | Yes, execution naturality only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.InfiniteTrajectory` | Canonical | Infinite discrete-event path law, stopping, and convergence | `Infinite` | — | Yes, discrete paths | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.InfiniteExecution` | Canonical | Observed behavioral specialization of infinite discrete execution | `Infinite` | — | Yes, adapter only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.GameTree` | Frontend | Finite no-chance inductive tree syntax | explicit module or `EconCSLib` | compile with `GameTreeOccurrenceObserved` for canonical EFG semantics | Yes, structural algorithms | Keep | F |
| `EconCSLib.GameTheory.ExtensiveGame.BackwardInduction` | Frontend | Computable structural backward-induction values | explicit module or `EconCSLib` | occurrence compiler for game-bound standard SPE | Yes, tree algorithms | Keep | F |
| `EconCSLib.GameTheory.ExtensiveGame.StochasticGameTree` | Frontend | Finite stochastic occurrence-sensitive tree syntax | `Compile` | `StochasticGameTree.toObservedChanceGame` | Yes, tree-local algorithms | Keep | F |
| `EconCSLib.GameTheory.ExtensiveGame.ImperfectInformation` | Frontend | Compact finite-state information-labeled syntax | `Compile` | `FiniteImperfectGame.ObservedCompiler` | Yes, input structure only | Keep | F |
| `EconCSLib.GameTheory.ExtensiveGame.FiniteArenaExtraction` | Frontend | Assumption-explicit Arena-to-tree extraction relation | explicit module | canonical Arena/observed layer when extraction is unnecessary | Yes, extraction only | Keep | F |
| `EconCSLib.GameTheory.ExtensiveGame.Zermelo` | Frontend | Chance-free finite two-player zero-sum tree theorem | explicit module or `EconCSLib` | canonical EFG only for representation-neutral extensions | Yes, specialized algorithm theory | Keep | F |
| `EconCSLib.GameTheory.ExtensiveGame.ZeroSumGameTreeWithChance` | Frontend | Exact rational binary chance-tree value and saddle algorithms | explicit module or `EconCSLib` | no equivalent replacement; compiler required before general EFG transfer | Yes, exact rational algorithms | Keep | F |
| `EconCSLib.GameTheory.ExtensiveGame.Compiler.FiniteImperfectObserved` | Frontend | Compact imperfect-information to observed/chance EFG compilation | `Compile` | target is `ObservedGame`/`ObservedChanceGame` | Yes, preservation only | Keep | F |
| `EconCSLib.GameTheory.ExtensiveGame.Compiler.StochasticGameTreeObserved` | Frontend | Stochastic-tree to occurrence-sensitive observed-chance compilation | `Compile` | target is `ObservedChanceGame` | Yes, preservation only | Keep | F |
| `EconCSLib.GameTheory.ExtensiveGame.Compiler.GameTreeOccurrenceObserved` | Frontend | Canonical root-bound occurrence-sensitive tree compiler and pure standard SPE | `Compile` | target is `ObservedGame` | Yes, compiler preservation | Keep | F |
| `EconCSLib.GameTheory.ExtensiveGame.Compiler.GameTreeObserved` | Historical | Endpoint-observed compiler preserving old endpoint policies | `Compile` | `GameTreeOccurrenceObserved` for occurrence-sensitive semantics | Bugfix/preservation only | Keep | H |
| `EconCSLib.GameTheory.ExtensiveGame.GameTreeSPE` | Historical | Global structural endpoint-policy optimality | explicit module | occurrence compiler for standard EFG SPE; not definitionally equivalent | Bugfix only | Keep | H |
| `EconCSLib.GameTheory.ExtensiveGame.GameTreeNE` | Historical | Root Nash and endpoint-policy restriction theorems | explicit module | canonical observed continuation Nash for new general theory | Bugfix only | Keep | H |
| `EconCSLib.GameTheory.ExtensiveGame.GameTreeStrategicForm` | Historical | Endpoint-plan strategic-form extraction | explicit module | occurrence observed-game pure profiles for occurrence plans | Bugfix only | Keep | H |
| `EconCSLib.GameTheory.ExtensiveGame.Strategy` | Historical | State-indexed Arena strategies without observed information | explicit module | `ObservedGame.PureStrategy`; semantics differ | Bugfix only | Documentation only | H |
| `EconCSLib.GameTheory.ExtensiveGame.Subgame` | Historical | State re-rooting and reachable-state restriction | `Core` | `ObservedGame.SubgameSystem` for lawful subgames; semantics differ | Bugfix only | Documentation only | H |
| `EconCSLib.GameTheory.ExtensiveGame.Play` | Compatibility | Former play path forwarding to stopped execution | `Finite` or `Execution.StoppedExecution` | `Arena.stoppedHistory[From]` | No implementation | Thin wrapper | W |
| `EconCSLib.GameTheory.ExtensiveGame.BehaviorStrategy` | Compatibility | Former invalid state-behavior path forwarding to observed behavior | `Finite`/`EqD` | information-indexed behavioral profiles plus chance kernel | No implementation | Thin wrapper | W |

## FOSG frontend

| Module | Status | Responsibility | Recommended import | Replacement | May grow | Action | Removal policy |
|---|---|---|---|---|---|---|---|
| `EconCSLib.GameTheory.ExtensiveGame.FOSG.FOSG` | Frontend | Compact simultaneous stochastic game and weak-serialization contract | `Compile` | compile/serialize to observed chance EFG | Yes, frontend only | Keep | F |
| `EconCSLib.GameTheory.ExtensiveGame.FOSG.FOSGBehavioralSerialization` | Frontend | Reusable strategic bridge for weak serializers | `Compile` | canonical continuation simulation is its target | Yes, preservation only | Keep | F |
| `EconCSLib.GameTheory.ExtensiveGame.FOSG.FOSGContinuation` | Frontend | Macro-root continuation and Nash transfer | `Compile` | canonical declared-root continuation semantics | Yes, FOSG transfer only | Keep | F |
| `EconCSLib.GameTheory.ExtensiveGame.FOSG.FOSGSequentialization` | Compatibility | Established sequentialization aggregate | `Compile` | `FOSG.Sequentialization.*` leaves | No implementation | Thin wrapper | W |
| `EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.Core` | Internal | Serialized micro-state/game construction | `Compile` | facade | Yes, implementation | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.Policy` | Internal | Source and target policy compilation | `Compile` | facade | Yes, implementation | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.MacroLaw` | Internal | Exact one-macro-step law | `Compile` | facade | Yes, implementation | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.Trajectory` | Internal | Iterated micro/macro trace law | `Compile` | facade | Yes, implementation | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.Witness` | Internal | Weak-serialization certificate assembly | `Compile` | facade | Yes, implementation | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.FOSG.Sequentialization.Equilibrium` | Internal | Finite-horizon Nash transfer from the witness | `Compile` | facade | Yes, implementation | Keep | I |

## Canonical observed EFG

The complete `Observed.Controlled` hierarchy is governed by the role taxonomy
in [`efg-controlled-api.md`](efg-controlled-api.md). `Controlled.Infrastructure`
and `Controlled.Morphism` are canonical declaration-free aggregate facades;
payoff-aware projection code is isolated under `Controlled.Compat` rather than
forming alternative canonical owners.

| Module | Status | Responsibility | Recommended import | Replacement | May grow | Action | Removal policy |
|---|---|---|---|---|---|---|---|
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Game` | Canonical | State-payoff observed-game information, two-way payoff attachment/erasure, bijective player/payoff reindexing, external root presentations, and compatibility names for controlled lawful systems | `Finite` | `Controlled`/`Controlled.Infrastructure.Subgame` for payoff-free clients | Yes, payoff-aware structure and adapters | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled` | Canonical | Payoff-free observed control, bijective player relabeling, pure-profile reindexing, and external root presentations | `Core` | — | Yes, objective-free information only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure` | Canonical | Declaration-free aggregate facade for controlled execution, well-formedness, subgame, finite, quasistrategy, recall, and winning infrastructure | narrowest defining `Controlled.Infrastructure.*` leaf | responsibility leaves | No declarations | Aggregate facade | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Core` | Canonical | No-chance mover helpers, pure-profile history execution, and player-strategy play compatibility | `Core` | — | Yes, execution helpers only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.WellFormed` | Canonical | General represented-information and mover-coherence certificates without finite, length, or execution assumptions | `Core` | — | Yes, general well-formedness only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Subgame` | Canonical | Occurrence-sensitive continuations, lawful/complete subgame systems, and bijective player-relabel transport | `Core` | — | Yes, subgame structure only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Finite` | Canonical | Uniform history-length, finite reachable-action/information, and finite-EFG certificate package | `Core` | — | Yes, finite certificates only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Quasi` | Canonical | Objective-free quasistrategy permissions, refinement, and play compatibility | `Core` | — | Yes, quasistrategy structure only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Infrastructure.Recall` | Canonical | Personal decisions, own-decision histories, classic/signal/public recall, no-absent-mindedness, and recall certificates | `Core` | — | Yes, recall only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Compat.Infrastructure` | Internal | `ObservedGame` projection and legacy recall/quasistrategy compatibility lemmas | downstream compatibility modules | payoff-free declarations in `Controlled.Infrastructure` | Adapter declarations only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism` | Canonical | Declaration-free aggregate facade for payoff-free structural, lawful-subgame, and recall morphism leaves | `Relations` or the narrowest `Controlled.Morphism.*` leaf | responsibility leaves | No declarations | Aggregate facade | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Core` | Canonical | Payoff-free Hom, information refinement, strict Iso, carrier/history/action/strategy maps, root-presentation comparison, inverse, and Iso algebra | `Relations` | — | Yes, structural morphisms only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Subgame` | Canonical | Strict-Iso preservation of occurrence-sensitive continuation, lawful roots, and selected/complete subgame systems | `Relations` | — | Yes, subgame transport only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Morphism.Recall` | Canonical | Strict-Iso preservation of personal decisions, own-decision histories, signal histories, and classic/private/public recall | `Relations` | — | Yes, recall transport only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Compat.Morphism` | Internal | Payoff-aware strict-isomorphism commuting square and legacy-Iso projection | `Relations` | `ControlledObservedGame.Iso` plus an external payoff square | Adapter declarations only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law.Discrete` | Canonical | Payoff-free discrete chance kernels and exact bounded complete-history PMF semantics | `Finite` | — | Yes, finite discrete laws only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Compat.DiscreteLaw` | Internal | Forget-payoff adapter from `ObservedChanceGame` to discrete controlled chance | `Finite` | `DiscreteControlledObservedChanceGame` | Adapter declarations only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law` | Canonical | Lawful complete-path probability semantics, measurable interpretations, same/cross-game realizations, and strict-Iso bridges | `Interface.Relations` | — | Yes, representation-independent law semantics only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law.DiscretePath` | Canonical | Discrete behavioral/PMF implementation of the common lawful complete-path probability carrier | `Infinite` | — | Yes, discrete constructor only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Law.Analytic` | Canonical | Measurable-kernel adapter to the common lawful complete-path probability carrier | `Analytic` | — | Yes, analytic adapter only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.WellFormed` | Canonical | Full information representation, decision coherence, and structural finite-EFG certificates | `Core` | — | Yes, hypothesis packages only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.FiniteUnfolding` | Canonical | Finite occurrence-sensitive reachable-history extraction with strict structural, root/subgame, recall, chance, strategy/update, and bounded-history-law preservation | `Finite` | — | Yes, extraction/preservation only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.SignalRecall` | Internal | Legacy `ObservedGame` names projected from the payoff-free private/public recall implementation | downstream legacy modules | `Controlled.Infrastructure` | Adapter declarations only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.SemanticMode` | Canonical | Lightweight strategy/chance semantic classification tags | `Relations` | — | Yes, classification only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Quasi` | Internal | Legacy `ObservedGame` quasistrategy names projected from the payoff-free implementation | downstream legacy modules | `Controlled.Infrastructure` | Adapter declarations only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Chance` | Canonical | Normalized chance kernels and chance isomorphisms | `Finite` | — | Yes, chance semantics | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Behavior` | Canonical | Information-indexed behavioral profiles and history policies | `Finite` | — | Yes, finite execution | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Controlled.Semantics` | Canonical | Payoff-free horizon/law-parametric continuation semantics and complete standard-SPE transfer boundary | explicit module or `EqD` | — | Yes, generic semantics only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Semantics` | Canonical | State-payoff `ObservedGame` compatibility surface for controlled continuation semantics | `EqD` | `Controlled.Semantics` for payoff-free clients | Adapter declarations only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.SPE` | Canonical | Total pure execution, lawful-root and standard SPE | `EqD` | — | Yes, canonical equilibrium | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.PerfectRecall` | Internal | Legacy `ObservedGame` classic-recall names and strict-Iso adapters projected from payoff-free theory | downstream legacy modules | `Controlled.Infrastructure`/`Controlled.Morphism` | Adapter declarations only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Mixed` | Canonical | Mixed complete plans and bounded mixed execution | `EqD` | — | Yes, mixed semantics | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.General` | Canonical | Countably supported general strategies over behavioral plans | `EqD` | — | Yes, carrier and lawful realization only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.LawEquivalence` | Canonical | Bounded complete-history-law realizations and terminal/payoff pushforwards | `EqD` | — | Yes, discrete semantic relations | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.PathLawEquivalence` | Internal | Payoff-aware names projected from the unique controlled complete-path law carrier | `Interface.Relations` | `Controlled.Law` | Adapter declarations only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Winning.Determinacy` | Canonical | Logical determinacy predicates, imperfect-information boundary, and proved finite perfect-information two-player zero-sum determinacy | `Interface.Winning` | — | Yes, assumption-explicit determinacy only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Winning.BasicCompat` | Internal | Legacy payoff-aware winning-strategy compatibility layer | `Interface.Winning` | payoff-free declarations in `Winning.Basic` | Adapter declarations only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Winning.DeterminacyCompat` | Internal | Legacy `ObservedGame` determinacy packages and well-formedness bridges | `Interface.Winning` | payoff-free declarations in `Winning.Determinacy` | Adapter declarations only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Winning.Chance` | Canonical | Almost-sure winning under discrete infinite history laws | `Interface.Winning.Stochastic` | — | Yes, stochastic winning only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Realization` | Canonical | Law-valued behavioral realization adapters | `EqD` | — | Yes, realization only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Continuation` | Canonical | Pure/behavioral compilation to continuation forms | `EqD` | — | Yes, adapter only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Kuhn` | Canonical | Finite hypotheses and behavioral-to-mixed realization | `EqD` | — | Yes, finite Kuhn only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.StrategyBridge` | Canonical | Uniform public navigation across strategy modes | `EqD` | — | Yes, navigation only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.BehaviorMorphism` | Canonical | Strict behavioral transport and Nash equivalence | `EqD` | — | Yes, strict transfer | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.MorphismHierarchy` | Canonical | Relation hierarchy and agreement regressions | `EqD` | — | Yes, hierarchy only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism` | Compatibility | Established strict-morphism aggregate | `EqD`/`Relations` | split `Observed.Morphism.*` leaves | No implementation | Thin wrapper | W |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Fiber` | Internal | Legacy forwarding import for neutral dependent-fiber helpers | `Relations` | `Execution.DependentFiber` | No new declarations | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Structural` | Canonical | Strict observed-EFG isomorphism structure | `Relations` | — | Yes, structural relation | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Inverse` | Internal | Inverse structural transport proofs | `Relations` | facade | Yes, proof helpers | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Operational` | Canonical | Exact finite execution transport | `Relations` | — | Yes, transfer only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Continuation` | Canonical | Total continuation and lawful-system transport | `EqD` | — | Yes, transfer only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Refinement` | Compatibility | Established information-refinement aggregate | `EqD`/`Relations` | split `Observed.Refinement.*` leaves | No implementation | Thin wrapper | W |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Refinement.Structural` | Canonical | Information-refinement structure and maps | `Relations` | — | Yes, structural relation | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Refinement.Core` | Canonical | Pure bounded execution and directional Nash transfer | `EqD` | — | Yes, transfer only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.Refinement.Termination` | Canonical | Termination-certified refinement transfer | `EqD` | — | Yes, transfer only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.BehaviorRefinement` | Compatibility | Established behavioral-refinement aggregate | `EqD`/`Relations` | split leaves | No implementation | Thin wrapper | W |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.BehaviorRefinement.Structural` | Canonical | Chance-aware refinement and strategy lifting | `Relations` | — | Yes, structural relation | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.BehaviorRefinement.Execution` | Canonical | Behavioral execution and directional Nash transfer | `EqD` | — | Yes, transfer only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Relations.Preservation` | Canonical | Formal preservation-matrix certificate aliases, coupling interfaces, and compiler-specific strict/weak packages | `Interface.Relations` | — | Yes, relation vocabulary and packages only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.DeferredSampling` | Compatibility | Established deferred-sampling aggregate | `EqD` | split leaves | No implementation | Thin wrapper | W |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.DeferredSampling.Core` | Internal | Fresh information keys and finite table laws | `EqD` | facade | Yes, proof implementation | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.DeferredSampling.Execution` | Internal | Fresh-query execution equivalence | `EqD` | facade | Yes, proof implementation | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.DeferredSampling.Realization` | Internal | Deferred behavioral/mixed continuation transfer | `EqD` | facade | Yes, proof implementation | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning` | Compatibility | Established conditioning aggregate | `EqD` | split leaves | No implementation | Thin wrapper | W |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Posterior` | Internal | Posterior conditioning of complete plans | `EqD` | facade | Yes, proof implementation | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Core` | Internal | Posterior products and recall identities | `EqD` | facade | Yes, proof implementation | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Execution` | Internal | Sequential posterior execution equality | `EqD` | facade | Yes, proof implementation | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Observed.KuhnConditioning.Realization` | Internal | Root-scoped mixed-to-behavioral law transfer | `EqD` | facade | Yes, proof implementation | Keep | I |

## Public interfaces

| Module | Status | Responsibility | Recommended import | Replacement | May grow | Action | Removal policy |
|---|---|---|---|---|---|---|---|
| `EconCSLib.GameTheory.ExtensiveGame.Interface.StructuralCore` | Canonical | Exact five-module structural facade for Arena, reachability, typed histories, complete plays, and payoff-free observed control | `Structural` | — | Yes, structural closure only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Core` | Canonical | Stable Foundation Facade for typed histories, finite/subgame/recall certificates, and bounded deterministic/PMF execution | `Core` | — | Yes, foundation families only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Objective` | Canonical | Stable measure-free outcome, winning-condition, and quasistrategy facade | `Interface.Objective` | — | Yes, no probability/equilibrium | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Winning` | Canonical | Stable logical winning-strategy and determinacy facade | `Interface.Winning` | — | Yes, no stochastic/analytic winning | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Winning.Stochastic` | Canonical | Stable discrete infinite almost-sure-winning facade | `Interface.Winning.Stochastic` | — | Yes, no non-atomic analytic arena | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Finite` | Canonical | Stable measure-free deterministic/PMF execution facade | `Finite` | — | Yes, finite execution only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Infinite` | Canonical | Stable measure-valued discrete-path facade | `Infinite` | — | Yes, infinite discrete only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Analytic` | Canonical | Stable non-atomic measurable-kernel execution facade | `Analytic` | — | Yes, execution/presentation only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Relations.Discrete` | Canonical | Stable structural/PMF relation facade | `Relations` | — | Yes, relation only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Discrete` | Canonical | Stable pure/behavioral/mixed/general finite equilibrium facade | `EqD` | — | Yes, discrete equilibrium only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium.Analytic` | Canonical | Stable measurable outcome and continuation-equilibrium facade | `EqA` | — | Yes, no restart/compiler | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Restart` | Canonical | Stable fresh-restart compatibility facade | `Restart` | — | Yes, canonical routes only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Compilation.Discrete` | Canonical | Stable finite compiler and FOSG serialization facade | `Compile` | — | Yes, compilers only | Keep | C |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Discrete` | Compatibility | Historical finite-plus-infinite discrete aggregate | `Finite` or `Infinite` | choose by horizon/law need | No implementation | Thin wrapper | W |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Relations` | Compatibility | Historical relations plus analytic-execution aggregate | `Relations` and optionally `Analytic` | granular facades | No implementation | Thin wrapper | W |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Equilibrium` | Compatibility | Historical discrete-plus-analytic equilibrium aggregate | `EqD` or `EqA` | granular facade | No implementation | Thin wrapper | W |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.Compilation` | Compatibility | Historical compiler plus analytic-equilibrium aggregate | `Compile` and optionally `EqA` | granular facades | No implementation | Thin wrapper | W |
| `EconCSLib.GameTheory.ExtensiveGame.Interface.SimulationFramework` | Compatibility | Complete historical EFG stack aggregate | smallest granular facade | granular facades | No implementation | Thin wrapper | W |

## Simulation implementation

The logical responsibility and physical-move decision for every module in
this section are recorded in the Simulation matrix in
[`efg-governance.md`](efg-governance.md).  None is a separately promised
public import path.

| Module | Status | Responsibility | Recommended import | Replacement | May grow | Action | Removal policy |
|---|---|---|---|---|---|---|---|
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.DiscreteBridge` | Internal | Exact discrete-path/analytic-path coherence | `Analytic` | facade | Yes, bridge only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.Arena` | Internal | Non-atomic analytic arena and discrete embedding | `Analytic` | facade | Yes, analytic core | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.Execution` | Internal | Legal terminal-aware analytic one-step policy | `Analytic` | facade | Yes, execution only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.Endpoint` | Internal | Finite analytic endpoint iteration | `Analytic` | facade | Yes, execution only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.StatePath` | Internal | Infinite state-path probability law | `Analytic` | facade | Yes, execution only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.HistoryPath` | Internal | Prefix-dependent state-history policy execution | `Analytic` | facade | Yes, execution only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.EventPath` | Internal | Joint state/action event-path execution | `Analytic` | facade | Yes, execution only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.ObservedEvent` | Internal | Fixed information-indexed event policies | `Analytic` | facade | Yes, presentation only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Kernel.RealizedInformation` | Internal | Abstract action realization for observed event policies | `Analytic` | facade | Yes, presentation only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Continuation.Path` | Internal | Absolute-prefix analytic continuation paths | `EqA` | facade | Yes, continuation only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Continuation.Conditioning` | Internal | Raw positive-prefix conditional-law bridge | `EqA` | facade | Yes, conditioning only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.KernelBridge` | Internal | Complete-history observed PMF-to-kernel bridge | `Analytic` | facade | Yes, bridge only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.Realized` | Internal | Explicit observed-chance realization certificate | `Analytic` | facade | Yes, presentation only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.Countable` | Internal | Automatic countable observed-chance analytic presentation | `Analytic` | facade | Yes, presentation only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.MeasurableHistory` | Internal | Explicit measurable complete-history model | `Analytic` | facade | Yes, presentation only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.Measurable` | Internal | Explicit uncountable observed-chance presentation | `Analytic` | facade | Yes, presentation only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Chance.ProfileAssembly` | Internal | Compatibility seam from PMF profiles to measurable assembly | `Analytic` | facade | Yes, adapter only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Kernel.Core` | Internal | Non-atomic observed kernel-valued strategy presentation | `Analytic` | facade | Yes, presentation only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Presentation.Kernel.ProfileAssembly` | Internal | Measurable player profiles and unilateral deviations | `Analytic` | facade | Yes, assembly only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Equilibrium.Outcome` | Internal | Path utilities, Nash, termination, and payoff convergence | `EqA` | facade | Yes, outcome/equilibrium | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Continuation.Observed` | Internal | Absolute/fresh continuation outcomes and equilibrium | `EqA` | facade | Yes, continuation/equilibrium | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Continuation.ObservedConditioning` | Internal | Observed lift of conditional continuation | `EqA` | facade | Yes, conditioning only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Core` | Internal | Root-event normalization and finite splicing | `Restart` | facade | Yes, restart proof | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Trajectory` | Internal | Spliced trajectory and finite-prefix laws | `Restart` | facade | Yes, restart proof | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Certificates` | Internal | Raw step/action/path restart certificates | `Restart` | facade | Yes, restart proof | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Observed` | Internal | Observed-profile lift to state-law compatibility | `Restart` | facade | Yes, restart proof | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Assembly` | Internal | Baseline-and-deviation compatibility assembly | `Restart` | facade | Yes, restart proof | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Equilibrium` | Internal | Canonical restart/continuation equilibrium transfer | `Restart` | facade | Yes, canonical route only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.Restart.Factorization` | Internal | Statistic and information-rebase certificate constructors | `Restart` | facade | Yes, constructors only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Simulation.ObservedMeasurableKernelRestartCompatibility` | Compatibility | Established complete restart implementation aggregate | `Restart` | restart leaves/facade | No implementation | Thin wrapper | W |

## Discrete execution and relation implementations

These internal modules were moved out of the historical `Simulation/`
directory on 2026-07-30. Their namespaces and public facade declarations did
not change; only non-promised implementation import paths changed.

| Module | Status | Responsibility | Recommended import | Replacement | May grow | Action | Removal policy |
|---|---|---|---|---|---|---|---|
| `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.KernelArena` | Internal | Discrete stochastic arena and policy kernel | `Finite`/`Relations` | facade | Yes, discrete kernel only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.KernelTrajectory` | Internal | Discrete policy execution, traces, and coupling transfer | `Finite`/`Relations` | facade | Yes, PMF execution/relations | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Relations.Discrete.KernelWeakSimulation` | Internal | Positive-fuel weak/stuttering kernel simulation | `Relations` | facade | Yes, relation only | Keep | I |
| `EconCSLib.GameTheory.ExtensiveGame.Relations.Discrete.Morphism` | Internal | Arena homomorphism, simulation, bisimulation, and weak simulation | `Relations` | facade | Yes, structural relation | Keep | I |

## Probability compatibility paths and reusable PMF mathematics

| Module | Status | Responsibility | Recommended import | Replacement | May grow | Action | Removal policy |
|---|---|---|---|---|---|---|---|
| `EconCSLib.GameTheory.ExtensiveGame.Probability.ConditionalSampling` | Compatibility | Former EFG-local conditioning path | `PMF` or `PMF.ConditionalSampling` | Math probability module | No implementation | Thin wrapper | W |
| `EconCSLib.GameTheory.ExtensiveGame.Probability.ConditionalProduct` | Compatibility | Former EFG-local conditional-product path | `PMF` or `PMF.ConditionalProduct` | Math probability module | No implementation | Thin wrapper | W |
| `EconCSLib.GameTheory.ExtensiveGame.Probability.DeferredSampling` | Compatibility | Former EFG-local deferred-sampling path | `PMF` or `PMF.DeferredSampling` | Math probability module | No implementation | Thin wrapper | W |
| `EconCSLib.GameTheory.ExtensiveGame.Probability.FiniteProductCoupling` | Compatibility | Former EFG-local finite-product/coupling aggregate | focused `PMF.*` module | Math probability modules | No implementation | Thin wrapper | W |
| `EconCSLib.Math.Probability.PMF` | Canonical | Stable reusable PMF aggregate | `PMF` | — | Yes, aggregate imports only | Keep | C |
| `EconCSLib.Math.Probability.PMF.Equiv` | Canonical | PMF pushforward equivalences | `PMF` or focused module | — | Yes, probability only | Keep | C |
| `EconCSLib.Math.Probability.PMF.FiniteProduct` | Canonical | Finite dependent independent products | `PMF` or focused module | — | Yes, probability only | Keep | C |
| `EconCSLib.Math.Probability.PMF.Coupling` | Canonical | Relation-supported exact PMF couplings | `PMF` or focused module | — | Yes, probability only | Keep | C |
| `EconCSLib.Math.Probability.PMF.ToMeasure` | Canonical | Exact PMF/Giry bind compatibility | `PMF` or focused module | — | Yes, probability only | Keep | C |
| `EconCSLib.Math.Probability.PMF.ConditionalSampling` | Canonical | Total discrete fiber conditioning | `PMF` or focused module | — | Yes, probability only | Keep | C |
| `EconCSLib.Math.Probability.PMF.ConditionalProduct` | Canonical | Conditional exposure in finite dependent products | `PMF` or focused module | — | Yes, probability only | Keep | C |
| `EconCSLib.Math.Probability.PMF.DeferredSampling` | Canonical | Representation-neutral fresh-query theorem | `PMF` or focused module | — | Yes, probability only | Keep | C |

## Representation-neutral game forms

| Module | Status | Responsibility | Recommended import | Replacement | May grow | Action | Removal policy |
|---|---|---|---|---|---|---|---|
| `EconCSLib.GameTheory.GameForm` | Canonical | Stable aggregate for representation-neutral semantics | `GF` | — | Yes, aggregate imports only | Keep | C |
| `EconCSLib.GameTheory.GameForm.Basic` | Canonical | Deterministic game forms, morphisms, and Nash transfer | `GF` | — | Yes, representation-neutral | Keep | C |
| `EconCSLib.GameTheory.GameForm.Law` | Canonical | Law-valued game forms and exact realization | `GF` | — | Yes, representation-neutral | Keep | C |
| `EconCSLib.GameTheory.GameForm.Continuation` | Compatibility | Established continuation-form aggregate | `GF` | split continuation leaves | No implementation | Thin wrapper | W |
| `EconCSLib.GameTheory.GameForm.Continuation.Core` | Canonical | Continuation forms and functional transfer | `GF` | — | Yes, representation-neutral | Keep | C |
| `EconCSLib.GameTheory.GameForm.Continuation.Simulation` | Canonical | Relational-root continuation simulation | `GF` | — | Yes, representation-neutral | Keep | C |
| `EconCSLib.GameTheory.GameForm.Continuation.Iso` | Canonical | Invertible continuation semantics | `GF` | — | Yes, representation-neutral | Keep | C |
| `EconCSLib.GameTheory.GameForm.IndexedContinuation` | Canonical | Arbitrary-index continuation adapter | `GF` | — | Yes, representation-neutral | Keep | C |
| `EconCSLib.GameTheory.GameForm.LimitSPE` | Historical | Uniform-limit Nash on caller-declared roots under a legacy path name | `GF` | `IndexedContinuationGameForm` plus the explicit convergence theorem; not standard SPE by itself | Bugfix only | Documentation only | H |

## Register invariants

1. A compatibility row contains imports and documentation only.
2. A historical row may receive correctness fixes and migration documentation,
   but no new parallel general Nash/SPE/continuation theory.
3. An internal row may move only when the move reduces a measured dependency
   or navigation cost; an old path remains a wrapper when removal would break a
   known client.
4. No module below `Math/Probability/PMF` imports EFG or game-theory modules.
5. Examples and open-problem modules are not part of this register and must not
   enter the stable root aggregate.
