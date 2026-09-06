/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Discrete.HistoryKernel

/-!
# Executable realization of finite abstract action laws

This module is the exact finite-law counterpart of the analytic realized
information interface.  An information policy first selects an abstract
action with a rational `FiniteLaw`; a fixed realization then selects a
concrete action in the dependent action fiber of the current state.  The two
finite choices compile by `FiniteLaw.bind`.

The abstract policy uses `Option (FiniteLaw ...)`.  `none` is required at
represented terminal prefixes, while a represented nonterminal prefix must
have a normalized finite law.  This is the executable analogue of a killed
analytic kernel: a normalized `FiniteLaw` is never used to pretend that a
probability law exists on an empty action type.

Concrete legality is enforced by the result type of `realizationLaw`.  It
returns `FiniteLaw (A.Action history.latestState)`, so compilation cannot put
mass in another state's dependent action fiber.  Mapping to
`A.ActionBundle` happens only after this typed realization.

This owner module is measure-free.  The weighted-Dirac interpretation and
the exact bridge to `MeasurableKernelArena.EventInformation.RealizedActionPolicy`
live in `Simulation.Kernel.FiniteRealizedInformation`.

## Main definitions

* `KernelArena.EventInformation` — an executable statistic of finite event
  prefixes;
* `EventInformation.ActionRealization` — finite concrete realization in the
  current dependent action fiber;
* `EventInformation.RealizedActionPolicy` — optional finite abstract laws at
  information values;
* `RealizedActionPolicy.abstractLawAt` and `realizedActionLaw` — the two local
  stages of executable action selection;
* `RealizedActionPolicy.realizedBundleLaw` — their exact `bind`/`map`
  compilation;
* `RealizedActionPolicy.toEventHistoryPolicy` — compilation to the ordinary
  action-recording finite executor.
-/

namespace KernelArena

universe uI uC

/-- A fixed, executable information statistic of finite event prefixes.

No enumeration of the information carrier is required: execution only
evaluates `informationAt` on the prefix currently being processed. -/
structure EventInformation (A : KernelArena) where
  /-- Information values available at each absolute event time. -/
  Information : ℕ → Type uI
  /-- Information represented by one complete finite event prefix. -/
  informationAt :
    (time : ℕ) → A.EventPrefix time → Information time

namespace EventInformation

variable {A : KernelArena}

end EventInformation
end KernelArena
