/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Interface.Execution.Analytic
import EconCSLib.GameTheory.ExtensiveGame.Interface.Relations.Discrete
import EconCSLib.GameTheory.ExtensiveGame.Observed.PathLawEquivalence
import EconCSLib.GameTheory.ExtensiveGame.Relations.Preservation

/-!
# EconCSLib.GameTheory.ExtensiveGame.Interface.Relations

Compatibility aggregate for structural/PMF relations and analytic execution.
It additionally exposes lawful complete-path probability semantics and
same-game/cross-game realization interfaces, whose semantic object is the
full path measure rather than only finite marginals.  Importing the interface
does not itself prove a path-law transfer for every compiler.
It also exposes the formal preservation-certificate vocabulary used by the
preservation matrix, including law realizations, couplings, strict/weak
relations, and compiler-specific packages.

New structural and PMF clients should import `Interface.Relations.Discrete`;
it exposes strict morphisms and isomorphisms, structural information
refinements, trajectory couplings, and weak/stuttering simulations without
the measure-valued execution stack. This established path retains its former
closure by combining that facade with `Interface.Execution.Analytic`.

Execution and analytic presentation construction are separately available
through the `Interface.Execution` tiers, so clients do not need to import
representation relations merely to run a model.
The relation hierarchy is deliberately semantic: clients should select the
strongest relation actually justified by their representation, rather than
coercing every compiler into a strict isomorphism.

Continuation/Nash transfer and termination-certified equilibrium transfer
belong to `Interface.Equilibrium.Discrete`; the complete analytic equilibrium
aggregate remains `Interface.Equilibrium`.
-/
