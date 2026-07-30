/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.Reachability

/-!
# EconCSLib.GameTheory.ExtensiveGame.Execution.History

Dependent histories and history unfolding for the Arena extensive-game model.

An Arena state is a world state, not necessarily a node of the unrolled game
tree: distinct paths may merge into the same state.  Information, recall, and
public-observation constructions therefore need histories as separate objects.
`Arena.History A start s` records a finite path from `start` whose endpoint is
`s`, while `Arena.unfoldFrom` turns those histories into the states of a
tree-shaped Arena.

## Main definitions

* `Arena.History` — a typed finite action history with a fixed start and endpoint.
* `Arena.HistoryFrom` — a history bundled with its endpoint.
* `Arena.unfoldFrom` — the history unfolding of an Arena.
* `ExtensiveGame.unfold` — the corresponding unfolding of a game, preserving
  movers and payoffs at history endpoints.

The unfolding is representation infrastructure.  It does not assert that the
original Arena is finite or acyclic, and it does not identify histories that
end in the same world state.
-/

namespace Arena

/-- A typed finite history in `A`, starting at `start` and ending at the state
indexed by the result type. -/
inductive History (A : Arena) (start : A.State) : A.State → Type _
  | nil : History A start start
  | snoc {s : A.State} (h : History A start s) (a : A.Action s) :
      History A start (A.next s a)

namespace History

variable {A : Arena} {start : A.State}

/-- Concatenate two typed histories whose intermediate endpoint agrees. -/
def append {middle finish : A.State}
    (first : A.History start middle)
    (suffix : A.History middle finish) :
    A.History start finish :=
  match suffix with
  | .nil => first
  | .snoc rest action => (first.append rest).snoc action

@[simp]
theorem append_nil {middle : A.State} (first : A.History start middle) :
    first.append (History.nil : A.History middle middle) = first := rfl

@[simp]
theorem append_snoc {middle finish : A.State}
    (first : A.History start middle)
    (suffix : A.History middle finish) (action : A.Action finish) :
    first.append (suffix.snoc action) =
      (first.append suffix).snoc action := rfl

@[simp]
theorem append_assoc {middle finish last : A.State}
    (first : A.History start middle)
    (second : A.History middle finish)
    (third : A.History finish last) :
    (first.append second).append third =
      first.append (second.append third) := by
  induction third with
  | nil =>
      rfl
  | snoc third action ih =>
      simp only [append_snoc, ih]

/-- The number of transitions in a history. -/
def length : {s : A.State} → A.History start s → ℕ
  | _, .nil => 0
  | _, .snoc h _ => h.length + 1

@[simp]
theorem length_nil :
    (History.nil : A.History start start).length = 0 := rfl

@[simp]
theorem length_snoc {s : A.State}
    (h : A.History start s) (a : A.Action s) :
    (h.snoc a).length = h.length + 1 := rfl

@[simp]
theorem length_append {middle finish : A.State}
    (first : A.History start middle)
    (suffix : A.History middle finish) :
    (first.append suffix).length = first.length + suffix.length := by
  induction suffix with
  | nil =>
      simp
  | snoc suffix action ih =>
      simp [ih, Nat.add_assoc]

/-- Forget the actions in a history and retain ordinary reachability of its
endpoint. -/
def toReachable {s : A.State} :
    (h : A.History start s) → A.Reachable start s
  | .nil => Arena.Reachable.refl _
  | .snoc h a => h.toReachable.tail a

end History

/-- A history from `start`, bundled with its endpoint.  This is the state type
of the history unfolding. -/
abbrev HistoryFrom (A : Arena) (start : A.State) :=
  Σ s : A.State, A.History start s

/-- The empty history at `start`. -/
def HistoryFrom.nil (A : Arena) (start : A.State) : A.HistoryFrom start :=
  ⟨start, History.nil⟩

/-- Unroll an Arena from `start`, using complete histories as states.

Two histories remain distinct even when their endpoints in `A` are equal. -/
def unfoldFrom (A : Arena) (start : A.State) : Arena where
  State := A.HistoryFrom start
  Action := fun h => A.Action h.1
  next := fun h a => ⟨A.next h.1 a, h.2.snoc a⟩

@[simp]
theorem unfoldFrom_next (A : Arena) (start : A.State)
    (h : A.HistoryFrom start) (a : A.Action h.1) :
    (A.unfoldFrom start).next h a = ⟨A.next h.1 a, h.2.snoc a⟩ := rfl

@[simp]
theorem unfoldFrom_isTerminal_iff (A : Arena) (start : A.State)
    (h : A.HistoryFrom start) :
    (A.unfoldFrom start).IsTerminal h ↔ A.IsTerminal h.1 := Iff.rfl

namespace History

variable {A : Arena} {start : A.State}

/-- Lift a suffix in the compact Arena to a history in the unfolding, starting
at the complete base history and ending at the appended complete history. -/
def liftAppend {middle finish : A.State}
    (baseHistory : A.History start middle)
    (suffix : A.History middle finish) :
    (A.unfoldFrom start).History
      ⟨middle, baseHistory⟩
      ⟨finish, baseHistory.append suffix⟩ :=
  match suffix with
  | .nil => .nil
  | .snoc rest action => (baseHistory.liftAppend rest).snoc action

@[simp]
theorem liftAppend_nil {middle : A.State}
    (baseHistory : A.History start middle) :
    baseHistory.liftAppend (History.nil : A.History middle middle) =
      History.nil := rfl

@[simp]
theorem liftAppend_snoc {middle finish : A.State}
    (baseHistory : A.History start middle)
    (suffix : A.History middle finish) (action : A.Action finish) :
    baseHistory.liftAppend (suffix.snoc action) =
      (baseHistory.liftAppend suffix).snoc action := rfl

@[simp]
theorem length_liftAppend {middle finish : A.State}
    (baseHistory : A.History start middle)
    (suffix : A.History middle finish) :
    (baseHistory.liftAppend suffix).length = suffix.length := by
  induction suffix with
  | nil =>
      rfl
  | snoc suffix action ih =>
      change (baseHistory.liftAppend suffix).length + 1 =
        suffix.length + 1
      rw [ih]

end History

/-- Every state in the history unfolding is reachable from the empty history. -/
theorem History.reachable_unfoldFrom (A : Arena) (start : A.State)
    {s : A.State} (h : A.History start s) :
    (A.unfoldFrom start).Reachable
      (HistoryFrom.nil A start) ⟨s, h⟩ := by
  induction h with
  | nil =>
      exact Arena.Reachable.refl _
  | snoc h a ih =>
      exact ih.tail a

end Arena

namespace ExtensiveGame

variable {N U : Type*}

/-- Unroll an extensive game into its history tree.

Movers and payoffs are read from the endpoint world state.  Observation and
information-state layers may instead distinguish histories with the same
endpoint. -/
def unfold (G : ExtensiveGame N U) : ExtensiveGame N U :=
  ofArena (G.toArena.unfoldFrom G.init)
    (Arena.HistoryFrom.nil G.toArena G.init)
    (fun h => G.mover h.1)
    (fun h i => G.payoff h.1 i)

@[simp]
theorem unfold_init (G : ExtensiveGame N U) :
    G.unfold.init = Arena.HistoryFrom.nil G.toArena G.init := rfl

@[simp]
theorem unfold_next (G : ExtensiveGame N U)
    (h : G.toArena.HistoryFrom G.init) (a : G.Action h.1) :
    G.unfold.next h a = ⟨G.next h.1 a, h.2.snoc a⟩ := rfl

@[simp]
theorem unfold_mover (G : ExtensiveGame N U)
    (h : G.toArena.HistoryFrom G.init) :
    G.unfold.mover h = G.mover h.1 := rfl

@[simp]
theorem unfold_payoff (G : ExtensiveGame N U)
    (h : G.toArena.HistoryFrom G.init) (i : N) :
    G.unfold.payoff h i = G.payoff h.1 i := rfl

@[simp]
theorem unfold_isTerminal_iff (G : ExtensiveGame N U)
    (h : G.toArena.HistoryFrom G.init) :
    G.unfold.isTerminal h ↔ G.isTerminal h.1 := Iff.rfl

/-- History unfolding preserves the absence of chance nodes. -/
theorem unfold_noChance (G : ExtensiveGame N U) (h : G.NoChance) :
    G.unfold.NoChance := by
  intro s hs
  exact h s.1 hs

/-- Every history-state is reachable from the initial empty history in the
unfolded game. -/
theorem unfold_isReachable (G : ExtensiveGame N U)
    (h : G.toArena.HistoryFrom G.init) :
    G.unfold.IsReachable h :=
  h.2.reachable_unfoldFrom G.toArena G.init

end ExtensiveGame
