/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.EffectivePathLaw
import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.RealizedInformation

/-!
# Executable finite kernel-valued behavioral profiles

This module is the measure-free effective subdomain of the analytic
`KernelBehavioralProfile` interface.  It keeps the same two-stage decision
model while replacing both stages by exact rational finite laws:

1. an information-indexed law selects an abstract action;
2. a prefix-dependent realization law selects a concrete dependent action.

`EffectiveKernelPresentation` owns the fixed information statistic, action
realization, executable terminal test, chance classifier, and concrete chance
law.  `EffectiveKernelBehavioralProfile` supplies only the abstract strategy
laws and proves that their concrete realization agrees with the fixed chance
law at chance prefixes.

The profile compiles through `EventInformation.RealizedActionPolicy`, then
reuses the ordinary finite event-history executor and coherent effective path
law.  No path law or expected value is supplied as an input to the algorithm.

Finite support at each input does not imply measurable dependence on a
general information carrier.  Consequently, the local weighted-Dirac
representation certificates and the exact bridge to the analytic
`KernelBehavioralProfile.compiledPolicy` live in
`Simulation.Presentation.Kernel.EffectiveBehavioralProfile`.

## Main definitions

* `KernelArena.EffectiveKernelPresentation` — fixed executable presentation
  data, including chance and terminal queries;
* `KernelArena.EffectiveKernelBehavioralProfile` — finite abstract strategy
  laws with exact realized-chance compatibility;
* `toRealizedActionPolicy` and `compiledPolicy` — the A06 finite realization
  compiler and its raw action-recording policy;
* `finitePrefixLawFrom` and `effectivePathLawFrom` — exact bounded and
  coherent finite-horizon execution.
-/

namespace KernelArena

universe uI uC

/-- Fixed executable data for a finite-law kernel-valued presentation.

The chance classifier is a Boolean so callers can query it directly.  Its
interpretation as a particular game's `mover = none` branch belongs to a
semantic representation certificate.  The chance law is typed in the
current dependent action fiber, making concrete legality structural. -/
structure EffectiveKernelPresentation (A : KernelArena) where
  /-- Executable statistic through which abstract strategy laws factor. -/
  information : EventInformation.{uI} A
  /-- Prefix-dependent finite realization of abstract actions. -/
  realization :
    EventInformation.ActionRealization.{uC} information
  /-- Explicit decision procedure for terminal states. -/
  terminalDecision :
    (state : A.State) → Decidable (IsEmpty (A.Action state))
  /-- Executable classifier for nonterminal chance prefixes. -/
  isChance :
    (time : ℕ) → A.EventPrefix time → Bool
  /-- Fixed concrete chance law at a represented nonterminal prefix. -/
  chanceLaw :
    (time : ℕ) →
      (history : A.EventPrefix time) →
      ¬ IsEmpty (A.Action history.latestState) →
      FiniteLaw (A.Action history.latestState)

end KernelArena
