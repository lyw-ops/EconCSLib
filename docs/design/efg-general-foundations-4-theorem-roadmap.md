# General EFG Foundations: Theorem and Delivery Roadmap

This is the implementation continuation of
[`efg-general-foundations-3-lean-api.md`](efg-general-foundations-3-lean-api.md).
Section numbering continues from the foundation documents.

Status: target architecture with Phase A complete and the foundational
Phase B/D carriers implemented. The finite occurrence-sensitive carrier,
complete-history/path-law comparison interfaces, recall hierarchy, and prefix
topology are now implemented. Finite perfect-information two-player zero-sum
logical determinacy and its structurally well-founded generalization are
proved on the payoff-free carrier. Arbitrary infinite Gale--Stewart existence
remains a theorem target. No remaining listed theorem is
considered formalized until a placeholder-free Lean declaration exists.

The following gaps are especially easy to overstate and remain explicit
theorem targets:

- full infinite path-law preservation for finite occurrence unfolding and for
  the individual frontends;
- a concrete infinite-horizon Kuhn path-law realization theorem;
- measurable analytic general-strategy spaces and their evaluation maps;
- Gale--Stewart open/closed and Borel determinacy beyond structural
  well-foundedness;
- frontend-specific action/information/chance/law/deviation/root transfer
  packages beyond the declarations each compiler currently proves.

## 16. Theorem ladder

The implementation order follows logical strength.

### 16.1 Structural play

1. finite length implies structural well-foundedness;
2. structural well-foundedness implies every legal complete play eventually
   reaches terminal absorption;
3. either condition implies a.s. termination for every supported stochastic
   executor;
4. finite-state alone implies none of these; retain a cyclic counterexample.

### 16.2 Perfect-information determinacy

First prove a measure-free theorem for two players, no chance, exclusive
winning sets, and singleton decision information:

1. backward determinacy from a uniform finite decision bound — implemented
   as `ControlledObservedGame.FiniteTwoPlayerHypotheses.isTwoPlayerDetermined`;
2. `Acc`-recursive determinacy from structural well-foundedness — implemented
   as `ControlledObservedGame.WellFoundedTwoPlayerHypotheses.isTwoPlayerDetermined`,
   with `WellFoundedPrefixHypotheses.isTwoPlayerDetermined` as the
   prefix-decision specialization;
3. terminal win/lose specialization;
4. compatibility with the existing finite `GameTree` Zermelo result.

Do not identify payoff saddle-value determinacy with logical winning
determinacy. Provide an embedding theorem for `0/1` zero-sum payoffs instead.

The semantic statement "every play reaches a decided prefix" and the
constructive `Acc` certificate should remain separate. A classical bridge may
be proved with its choice assumptions visible.

### 16.3 Open and closed games

After the finite and `Acc` tracks:

1. define prefix topology on complete plays — implemented;
2. characterize open winning sets by finite witnesses — implemented in the
   direction from finite-prefix decisions, with generated topology and
   measurability bridges;
3. prove the open/closed Gale-Stewart theorem, or connect to a Mathlib theorem
   if an exact one exists;
4. leave arbitrary and Borel determinacy outside the stable target until their
   foundational assumptions and proof cost are reviewed.

The finite length-two imperfect-information regression is implemented with
the payoff-free `ControlledObservedGame`: neither player has a pure pathwise
winning strategy. It cannot be bypassed by adding a fabricated payoff or a
history-indexed perfect-information strategy.

### 16.4 Utility equilibrium

For finite branching, finite length, and suitable finite player/action
hypotheses:

1. perfect-information backward induction with chance;
2. pure SPE for no-chance perfect-information games;
3. behavioral Nash existence under perfect recall via finite normal form plus
   Kuhn realization;
4. behavioral SPE existence by lawful-subgame continuation semantics;
5. exact terminal-law and expected-utility preservation.

Every existence statement must name its preference assumptions. Argmax
selection needs a finite nonempty action set and an appropriate total preorder
or linear order; expected utility additionally needs its algebra/order
structure.

### 16.5 Kuhn and general strategies

Extend the current bounded realization track in stages:

1. behavioral-to-mixed complete-plan law under finite information and no
   absent-mindedness;
2. root-scoped mixed-to-behavioral realization under perfect recall;
3. equality of complete terminal-history laws, not only one scalar payoff;
4. opponent general-strategy integration by equality of the conditional
   outcome kernel before integration;
5. analytic general strategies only after measurability is established.

The theorem should quantify against the declared opponent class. It must not
say "every general strategy" when only `PMF`-supported or measurable general
strategies have been constructed.

### 16.6 Infinite utility games

Reuse the analytic path layer:

- discounted objectives: bounded/integrable under explicit hypotheses;
- total reward: summability or domination required;
- limsup and mean payoff: measurability proved separately;
- terminal payoff: finite-bound or a.s.-termination route;
- nonterminating paths never receive an implicit terminal payoff.

Infinite-horizon Nash or SPE is theorem-local and objective-specific. No
general equilibrium existence theorem follows merely from representability.

## 17. Staged delivery

### Phase A - structural vocabulary

- implement `CompletePlay`, splice, and legality;
- implement length and `Acc` certificates;
- prove bridges to existing finite and infinite execution;
- expose an opt-in objective facade.

Progress: complete for deterministic stopped execution, the measure-free
objective facade, and the discrete infinite history law. `Arena.pathLaw` is
proved almost surely supported on the common unbundled complete-play legality
predicate.

The generic non-atomic `MeasurableKernelArena` is intentionally not coerced to
`Arena.CompletePlay`: its successor is a probability kernel rather than a
deterministic `Arena.next`. Its state/event path semantics remain in the
analytic layer. The established discrete-to-analytic embedding has an exact
whole-path equality theorem. Packaging an observed analytic executor into the
common `CompletePathLawSemantics` additionally requires the adapter's explicit
almost-sure canonical-history-legality premise.

Promotion gate: no duplicated path-law constructor and exact coordinate
recovery from every existing execution family.

### Phase B - objectives and finite profile

- implement terminal/path outcomes and winning conditions;
- add represented-information and finite-EFG certificates;
- extract the finite reachable history tree;
- compile existing finite frontends into the certificate where valid.

Promotion gate: exact action, information, chance, outcome, deviation, and
root preservation statements.

Progress: terminal/path outcomes, winning conditions, prefix-decision
certificates, full decision-information representation, mover coherence, the
structural `FiniteEFGHypotheses` package, and finite occurrence-sensitive
bounded-history extraction are implemented. Root-objective restriction
replays accumulated prefixes, and the canonical payoff-free
complete-information presentation uses only decision histories. The
extraction proves the finite carrier, a strict payoff-free structural
isomorphism, action/mover/observation/information pullbacks, a finite
discrete-chance presentation, pure/behavioral strategy and update transport,
external roots and lawful systems, terminal/path outcomes, all three recall
notions, merge distinction, length-bound preservation, and exact bounded
complete-history law pushforward. Full infinite path-law and
frontend-specific transfer remain explicit theorem tracks.

### Phase C - finite and well-founded theorems

- determinacy for finite and `Acc`-well-founded perfect-information games;
- chance-aware backward induction and pure/behavioral equilibrium results;
- negative imperfect-information and cyclic-state regressions.

Promotion gate: theorem assumptions match counterexample boundaries.

Progress: the finite and structurally well-founded no-chance
perfect-information two-player zero-sum determinacy theorems and the strict
two-step imperfect-information counterexample are complete.
Gale--Stewart/open-closed determinacy beyond structural well-foundedness
remains an explicit theorem track.

### Phase D - strategy completion

- discrete general and quasistrategies;
- complete-history-law Kuhn theorems;
- general-opponent integration;
- signal/public recall certificates.

Promotion gate: no strategy-space isomorphism claim where only realization or
deviation coverage has been proved.

Progress: payoff-free classic/private/public recall certificates and their
strict-isomorphism and finite-unfolding preservation theorems are implemented
in `Controlled.Infrastructure`/`Controlled.Morphism`; the legacy
`PerfectRecall`, `SignalRecall`, and `Quasi` modules are projections rather
than independent theories.
The public/private/classic non-implication boundaries have executable
regressions. Complete-history realization and full-path realization remain
separate relation strengths; target-deviation coverage is not inferred from
source-deviation mapping.

Progress: information-consistent quasistrategies and explicitly named
countably supported `DiscreteGeneralStrategy` carriers are implemented.
Pathwise and profile-based pure winning are separate, with bridge theorems and
strict imperfect-information regressions. Bounded complete-history-law
realizations preserve all source unilateral deviations componentwise and
expose reverse target-deviation coverage separately. The common full-path
carrier now forces normalization and almost-sure canonical legality; it has
measurable downstream interpretations, same-game and cross-game functional
realizations, and probability couplings. This is an interface and bridge
layer, not a proof of every intended representation theorem. A concrete
infinite-horizon cross-strategy Kuhn path-law theorem, full infinite
finite-unfolding/frontend path-law transfer, general-opponent integration
beyond the stated PMF-supported models, and analytic general strategies
remain targets.

### Phase E - analytic and topological objectives

- measurable mixed/general strategies;
- almost-sure winning;
- open/closed path objectives and determinacy;

Progress: almost-sure winning under the canonical discrete infinite history
law is implemented, requires an `IsProbabilityMeasure` certificate, and uses
the common almost-everywhere legality bridge. Arbitrary measures use the
separately named `AEWinningUnder`.
Prefix cylinders, prefix-open/closed events, finite-prefix decisions, and a
generated measurable space are implemented. The analytic layer already
supplies measurable state/history/event paths. Its non-atomic regression now
uses an actual generated-state-path cylinder, proves that it is measurable,
nonempty, and proper, and computes its probability as one half. A single
general non-atomic winning facade and
Gale--Stewart/Borel determinacy theorems remain targets.
- model-specific infinite-horizon equilibrium applications.

Promotion gate: all measurability, integrability, choice, and topological
assumptions appear explicitly.

### Phase F - assessments

- belief systems on reached and unreached information states;
- Bayesian consistency/regular conditional boundaries;
- sequential rationality and sequential equilibrium;
- refinements only after their finite mathematical definitions are stable.

Progress: an explicit opt-in experimental module now implements
occurrence-sensitive belief systems, finite Bayes normalization, assessments,
completely mixed perturbation/consistency certificates, and
evaluator-relative sequential rationality/equilibrium. It does not yet provide
the canonical conditional continuation-utility evaluator or the standard Nash
consequence, so it remains outside equilibrium facades. This phase must not
modify the base `ObservedGame` record.

## 18. Verification plan

Each implementation change runs the checks required by `AGENTS.md`, including
the EFG governance checker. Add focused regressions for:

- finite tree with chance and exact terminal law;
- finite-state self-loop with no termination;
- infinite ambient state with finite reachable unfolding;
- well-founded but not uniformly bounded branching;
- a.s.-terminating game with a nonterminating null branch;
- two-player finite determined perfect-information game;
- length-two undetermined imperfect-information game;
- path-dependent terminal outcome on two histories sharing one endpoint;
- winning objective decided only on an infinite play;
- absolute-prefix objective differing from fresh-clock restart;
- behavioral realization preserving the full terminal-history law;
- quasistrategy that has no deterministic selector without a visible choice
  assumption.

For executable finite predicates, follow the repository `Prop`/`Bool` rule:
the mathematical `Prop` is primary, the Boolean checker is secondary, and an
`isX_iff` theorem connects them.

## 19. Designs explicitly rejected

- adding `Fintype State` or acyclicity to `Arena`;
- defining "finite EFG" as finite state;
- using increasing fuel as the definition of an infinite game;
- assigning zero terminal payoff to every nonterminating path;
- encoding every winning condition only as a real-valued payoff;
- equating totality with determinacy;
- asserting determinacy for arbitrary winning sets or imperfect information;
- treating chance as an adversary and as a probability law in one predicate;
- merging mixed, behavioral, and general strategies;
- encoding quasistrategies as randomized strategies;
- defining information consistency by equality of endpoint states;
- using fresh restart for path-dependent subgame objectives;
- calling an endpoint-forgetting compiler an isomorphism;
- adding beliefs or sequential-equilibrium data to the base EFG structure.

## 20. Completion criteria

The foundation is complete when:

1. every finite textbook EFG has a documented route to
   `ObservedChanceGame` plus finite certificates;
2. finite, structurally well-founded, a.s.-terminating, and genuinely infinite
   games are expressible without changing the core carrier;
3. terminal, path-utility, and winning objectives share one legal-play
   semantics;
4. pure, behavioral, mixed, general, and quasi strategies are distinct and
   connected by correctly scoped realization theorems;
5. totality and determinacy are separate, with positive perfect-information
   and negative imperfect-information results;
6. Nash/SPE continue to reuse game-form and lawful-subgame infrastructure;
7. existing finite and analytic executors recover the new semantics through
   proved bridges;
8. no public theorem hides finiteness, choice, measurability, integrability,
   recall, or termination assumptions;
9. every compiler states its exact semantic preservation strength;
10. all modules are placeholder-free, governance-registered, and exposed only
    through the intended granular facades.
