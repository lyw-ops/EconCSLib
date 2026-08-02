/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.GameTreeStrategicForm
import EconCSLib.GameTheory.ExtensiveGame.Observed.SPE

/-!
# EconCSLib.GameTheory.ExtensiveGame.Compiler.GameTreeObserved

Compile a finite structural `GameTree` into an endpoint-observed
history-indexed extensive-game presentation.

A compiled state is a subtree.  At a node, a legal action is a child together
with evidence that it occurs in the node's nonempty child list.  Player and
public observations reveal the current subtree, while a decision information
state stores the full node context `(mover, head, tail)`.  Its indexed abstract
action type is definitionally the old `GameTree` child-choice type.

This compiler deliberately inherits the historical endpoint/global strategy
semantics: structurally equal subtree values have equal observations and node
information even when they occur at different complete histories. It is not
the canonical occurrence-sensitive perfect-information presentation. Use
`GameTreeOccurrenceObserved` when distinct history occurrences must be
distinguishable.

This module supplies validation targets for the observed-game design:

* one player's observed pure strategies are equivalent to
  `GameTree.PlayerStrategy`;
* stopped execution of a translated strategy reaches the same terminal payoff
  as `GameTree.outcome`;
* compiled histories correspond to `GameTree.Subtree` occurrences;
* the compiled game is pure terminating from every history root; and
* termination-certified observed Nash on presentation-designated
  continuations is equivalent to the existing root-scoped
  `GameTree.IsGlobalEndpointSubgamePerfectOn`.
-/

namespace GameTree

variable {N U : Type*}

/-! ### Base extensive game -/

/-- Legal actions in the Arena presentation of a tree. -/
def arenaAction : GameTree N U → Type _
  | .Leaf _ => PEmpty
  | .Node _ head tail => {child : GameTree N U // child ∈ head :: tail}

/-- Follow the child selected by a legal tree action. -/
def arenaNext :
    (g : GameTree N U) → arenaAction g → GameTree N U
  | .Leaf _, action => nomatch action
  | .Node _ _ _, action => action.1

/-- The root-independent Arena of `GameTree` states and child-selection
actions.  A particular compiled extensive game adds only its chosen initial
root, mover, and payoff fields. -/
def treeArena (N U : Type*) : Arena where
  State := GameTree N U
  Action := arenaAction
  next := arenaNext

/-- A total payoff field for the base `ExtensiveGame`.

Only leaf payoffs are semantically observed.  At a nonterminal node this picks
the head subtree's representative payoff solely to fill the deliberately total
base-game field. -/
def representativePayoff : GameTree N U → (N → U)
  | .Leaf payoff => payoff
  | .Node _ head _ => representativePayoff head

/-- View a finite structural tree as an `ExtensiveGame` whose states
are subtrees and whose actions select children. -/
def toExtensiveGame (root : GameTree N U) : ExtensiveGame N U where
  toArena := treeArena N U
  init := root
  mover
    | .Leaf _ => none
    | .Node mover _ _ => some mover
  payoff := representativePayoff

@[simp]
theorem toExtensiveGame_init (root : GameTree N U) :
    (toExtensiveGame root).init = root := rfl

@[simp]
theorem toExtensiveGame_action_leaf (root : GameTree N U) (payoff : N → U) :
    (toExtensiveGame root).Action (.Leaf payoff) = PEmpty := rfl

@[simp]
theorem toExtensiveGame_action_node (root : GameTree N U)
    (mover : N) (head : GameTree N U) (tail : List (GameTree N U)) :
    (toExtensiveGame root).Action (.Node mover head tail) =
      {child : GameTree N U // child ∈ head :: tail} := rfl

@[simp]
theorem toExtensiveGame_next_node (root : GameTree N U)
    (mover : N) (head : GameTree N U) (tail : List (GameTree N U))
    (action : (toExtensiveGame root).Action (.Node mover head tail)) :
    (toExtensiveGame root).next (.Node mover head tail) action = action.1 := rfl

@[simp]
theorem toExtensiveGame_mover_leaf (root : GameTree N U) (payoff : N → U) :
    (toExtensiveGame root).mover (.Leaf payoff) = none := rfl

@[simp]
theorem toExtensiveGame_mover_node (root : GameTree N U)
    (mover : N) (head : GameTree N U) (tail : List (GameTree N U)) :
    (toExtensiveGame root).mover (.Node mover head tail) = some mover := rfl

@[simp]
theorem toExtensiveGame_payoff_leaf (root : GameTree N U) (payoff : N → U) :
    (toExtensiveGame root).payoff (.Leaf payoff) = payoff := rfl

/-- Leaves are terminal in the compiled base game. -/
theorem toExtensiveGame_isTerminal_leaf (root : GameTree N U)
    (payoff : N → U) :
    (toExtensiveGame root).isTerminal (.Leaf payoff) :=
  ⟨fun action => nomatch action⟩

/-- Nodes are nonterminal in the compiled base game. -/
theorem toExtensiveGame_not_isTerminal_node (root : GameTree N U)
    (mover : N) (head : GameTree N U) (tail : List (GameTree N U)) :
    ¬ (toExtensiveGame root).isTerminal (.Node mover head tail) := by
  intro hterminal
  exact hterminal.false ⟨head, List.mem_cons_self⟩

/-- Terminality of the compiled tree game is decidable by inspecting the
subtree constructor. -/
def toExtensiveGame_terminalDecidable (root : GameTree N U) :
    (g : (toExtensiveGame root).State) →
      Decidable ((toExtensiveGame root).isTerminal g)
  | .Leaf payoff => isTrue (toExtensiveGame_isTerminal_leaf root payoff)
  | .Node mover head tail =>
      isFalse (toExtensiveGame_not_isTerminal_node root mover head tail)

instance toExtensiveGame.instTerminalDecidable (root : GameTree N U) :
    (g : (toExtensiveGame root).State) →
      Decidable ((toExtensiveGame root).isTerminal g) :=
  toExtensiveGame_terminalDecidable root

/-- The compiled structural tree has no chance nodes. -/
theorem toExtensiveGame_noChance (root : GameTree N U) :
    (toExtensiveGame root).NoChance := by
  intro g hnonterminal
  cases g with
  | Leaf payoff =>
      exact (hnonterminal
        (toExtensiveGame_isTerminal_leaf root payoff)).elim
  | Node mover head tail =>
      exact ⟨mover, rfl⟩

/-! ### Histories and designated continuation roots -/

/-- The endpoint of every compiled Arena history is a subtree of the original
root. -/
theorem arenaHistory_subtree {root : GameTree N U} :
    ∀ {g : GameTree N U},
      (treeArena N U).History root g → Subtree g root
  | _, .nil =>
      Subtree.self root
  | _, @Arena.History.snoc _ _ current history action => by
      have ih := arenaHistory_subtree history
      cases current with
      | Leaf payoff =>
          exact nomatch action
      | Node mover head tail =>
          exact
            (Subtree.child_mem mover head tail action.2).trans ih

/-- Every subtree occurrence has at least one corresponding compiled Arena
history from the original root. -/
theorem Subtree.arenaHistory_nonempty {subtree root : GameTree N U}
    (hsubtree : Subtree subtree root) :
    Nonempty ((toExtensiveGame root).toArena.History root subtree) := by
  induction hsubtree with
  | refl =>
      exact ⟨Arena.History.nil⟩
  | inHead mover head tail _ ih =>
      obtain ⟨rest⟩ := ih
      let first :
          (toExtensiveGame (.Node mover head tail)).toArena.Action
            (.Node mover head tail) :=
        ⟨head, List.mem_cons_self⟩
      exact ⟨(Arena.History.nil.snoc first).append rest⟩
  | inTail mover head tail hmem _ ih =>
      obtain ⟨rest⟩ := ih
      let first :
          (toExtensiveGame (.Node mover head tail)).toArena.Action
            (.Node mover head tail) :=
        ⟨_, List.mem_cons_of_mem head hmem⟩
      exact ⟨(Arena.History.nil.snoc first).append rest⟩

/-- Choose a compiled Arena history witnessing a subtree occurrence. -/
noncomputable def Subtree.toArenaHistory
    {subtree root : GameTree N U}
    (hsubtree : Subtree subtree root) :
    (toExtensiveGame root).toArena.History root subtree :=
  hsubtree.arenaHistory_nonempty.some

/-! ### Endpoint observations and decision information -/

/-- A node context, used as the decision information state in the compiled
endpoint-observed game. Equal node-context values at different occurrences are
intentionally identified. -/
structure NodeInfo (N U : Type*) where
  mover : N
  head : GameTree N U
  tail : List (GameTree N U)

namespace NodeInfo

/-- Reconstruct the tree node represented by a decision information state. -/
def tree (I : NodeInfo N U) : GameTree N U :=
  .Node I.mover I.head I.tail

/-- Abstract actions at a node information state. -/
def Action (I : NodeInfo N U) : Type _ :=
  {child : GameTree N U // child ∈ I.head :: I.tail}

end NodeInfo

/-- Extract the node context at a compiled player-controlled state. -/
def nodeInfoAt (root g : GameTree N U) (i : N)
    (hmover : (toExtensiveGame root).mover g = some i) :
    NodeInfo N U :=
  match g with
  | .Leaf _ => False.elim (by simp at hmover)
  | .Node mover head tail => ⟨mover, head, tail⟩

@[simp]
theorem nodeInfoAt_tree (root g : GameTree N U) (i : N)
    (hmover : (toExtensiveGame root).mover g = some i) :
    (nodeInfoAt root g i hmover).tree = g := by
  cases g with
  | Leaf payoff =>
      simp at hmover
  | Node mover head tail =>
      rfl

/-- The node-context action type and compiled Arena action type agree at every
player-controlled state. -/
def nodeActionEquiv (root g : GameTree N U) (i : N)
    (hmover : (toExtensiveGame root).mover g = some i) :
    (nodeInfoAt root g i hmover).Action ≃
      (toExtensiveGame root).Action g :=
  match g with
  | .Leaf _ => False.elim (by simp at hmover)
  | .Node _ _ _ => Equiv.refl _

/-- Compile a `GameTree` into an endpoint-observed extensive game.

Every player and the public observe the complete current subtree.  A
player-controlled history maps to the node context at its endpoint. Distinct
histories ending in structurally equal subtrees are not distinguished. -/
def toObservedGame (root : GameTree N U) :
    ExtensiveGame.ObservedGame N U where
  base := toExtensiveGame root
  Observation := fun _ => GameTree N U
  PublicObservation := GameTree N U
  observe := fun _ history => history.1
  publicObserve := fun history => history.1
  publicOf := fun _ observation => observation
  observe_public := by
    intro i history
    rfl
  InfoState := fun _ => NodeInfo N U
  infoObserve := fun _ info => info.tree
  infoAt := fun history i hmover =>
    nodeInfoAt root history.1 i hmover
  infoAt_observe := fun history i hmover =>
    nodeInfoAt_tree root history.1 i hmover
  InfoAction := fun _ info => info.Action
  actionEquiv := fun history i hmover =>
    nodeActionEquiv root history.1 i hmover

instance toObservedGame.instTerminalDecidable (root : GameTree N U) :
    (g : (toObservedGame root).base.State) →
      Decidable ((toObservedGame root).base.isTerminal g) :=
  toExtensiveGame_terminalDecidable root

/-! ### Strategy correspondence -/

/-- One player's pure strategies in the observed compilation are exactly the
existing complete contingent plans for `GameTree`. -/
def playerStrategyEquiv (root : GameTree N U) (i : N) :
    (toObservedGame root).PureStrategy i ≃ PlayerStrategy N U where
  toFun σ := fun mover head tail => σ ⟨mover, head, tail⟩
  invFun τ := fun info => τ info.mover info.head info.tail
  left_inv σ := by
    funext info
    cases info
    rfl
  right_inv τ := by
    funext mover head tail
    rfl

/-- Translate the old global tree strategy into an observed pure profile.
The outer player argument is irrelevant because the old global strategy
already dispatches on the mover stored in each node context. -/
def strategyToObservedProfile (root : GameTree N U) (σ : Strategy N U) :
    (toObservedGame root).PureProfile :=
  fun _ info => σ info.mover info.head info.tail

/-- Translate a strategic-form profile player by player into the observed
pure-profile type. -/
def playerProfileToObservedProfile (root : GameTree N U)
    (σ : N → PlayerStrategy N U) :
    (toObservedGame root).PureProfile :=
  fun i info => σ i info.mover info.head info.tail

/-- The terminal-aware base-history policy induced by a translated global
tree strategy. -/
def strategyHistoryPolicy (root : GameTree N U) (σ : Strategy N U) :
    (toExtensiveGame root).toArena.HistoryPolicy root :=
  (strategyToObservedProfile root σ).toHistoryPolicy
    (toObservedGame root) (toExtensiveGame_noChance root)

/-- The terminal-aware base-history policy induced by a translated
strategic-form player profile. -/
def playerProfileHistoryPolicy (root : GameTree N U)
    (σ : N → PlayerStrategy N U) :
    (toExtensiveGame root).toArena.HistoryPolicy root :=
  (playerProfileToObservedProfile root σ).toHistoryPolicy
    (toObservedGame root) (toExtensiveGame_noChance root)

/-- At a concrete node history, translating a global tree strategy prescribes
exactly its original child choice. -/
theorem strategyHistoryPolicy_node (root : GameTree N U)
    (σ : Strategy N U) (mover : N) (head : GameTree N U)
    (tail : List (GameTree N U))
    (history :
      (toExtensiveGame root).toArena.History root (.Node mover head tail))
    (hnonterminal :
      ¬ (toExtensiveGame root).isTerminal (.Node mover head tail)) :
    strategyHistoryPolicy root σ ⟨.Node mover head tail, history⟩
        hnonterminal =
      σ mover head tail := by
  rw [strategyHistoryPolicy,
    ExtensiveGame.ObservedGame.PureProfile.toHistoryPolicy_of_mover
      (toObservedGame root) _ _ _ _ mover rfl]
  rfl

/-- At a concrete node history, translating a player profile prescribes the
same action as `GameTree.profileStrategy`. -/
theorem playerProfileHistoryPolicy_node (root : GameTree N U)
    (σ : N → PlayerStrategy N U) (mover : N)
    (head : GameTree N U) (tail : List (GameTree N U))
    (history :
      (toExtensiveGame root).toArena.History root (.Node mover head tail))
    (hnonterminal :
      ¬ (toExtensiveGame root).isTerminal (.Node mover head tail)) :
    playerProfileHistoryPolicy root σ ⟨.Node mover head tail, history⟩
        hnonterminal =
      profileStrategy σ mover head tail := by
  rw [playerProfileHistoryPolicy,
    ExtensiveGame.ObservedGame.PureProfile.toHistoryPolicy_of_mover
      (toObservedGame root) _ _ _ _ mover rfl]
  rfl

/-! ### Result correspondence -/

/-- Any terminal-aware history policy that agrees with a `GameTree.Strategy`
at node histories reaches a leaf carrying `GameTree.outcome`, provided the
fuel is at least the current subtree's structural size. -/
theorem stoppedHistoryFrom_policy_reaches_outcome
    (root : GameTree N U) (σ : Strategy N U)
    (policy : (toExtensiveGame root).toArena.HistoryPolicy root)
    (hpolicy :
      ∀ (mover : N) (head : GameTree N U)
        (tail : List (GameTree N U))
        (history :
          (toExtensiveGame root).toArena.History root
            (.Node mover head tail))
        (hnonterminal :
          ¬ (toExtensiveGame root).isTerminal (.Node mover head tail)),
        policy ⟨.Node mover head tail, history⟩ hnonterminal =
          σ mover head tail)
    (g : GameTree N U)
    (history : (toExtensiveGame root).toArena.History root g)
    (fuel : ℕ) (hsize : g.size ≤ fuel) :
    ∃ payoff : N → U,
      ((toExtensiveGame root).toArena.stoppedHistoryFrom
        policy ⟨g, history⟩ fuel).1 = .Leaf payoff ∧
      payoff = outcome σ g := by
  let motive : GameTree N U → Prop := fun subtree =>
    ∀ (subhistory :
        (toExtensiveGame root).toArena.History root subtree)
      (subfuel : ℕ), subtree.size ≤ subfuel →
      ∃ payoff : N → U,
        ((toExtensiveGame root).toArena.stoppedHistoryFrom
          policy ⟨subtree, subhistory⟩ subfuel).1 = .Leaf payoff ∧
        payoff = outcome σ subtree
  apply GameTree.strong_induction (motive := motive)
  · intro payoff subhistory subfuel hsubsize
    refine ⟨payoff, ?_, by simp⟩
    rw [Arena.stoppedHistoryFrom_eq_self_of_terminal
      policy ⟨.Leaf payoff, subhistory⟩
      (toExtensiveGame_isTerminal_leaf root payoff) subfuel]
  · intro mover head tail ih subhistory subfuel hsubsize
    cases subfuel with
    | zero =>
        have hpositive := size_pos (.Node mover head tail)
        omega
    | succ subfuel =>
        have hnonterminal :=
          toExtensiveGame_not_isTerminal_node root mover head tail
        rw [Arena.stoppedHistoryFrom_succ_of_not_terminal
          policy ⟨.Node mover head tail, subhistory⟩
          subfuel hnonterminal]
        rw [hpolicy mover head tail subhistory hnonterminal]
        have hchildSize :
            (σ mover head tail).1.size ≤ subfuel := by
          have hlt := size_mem_children_lt mover head tail
            (by simpa [children] using (σ mover head tail).2)
          omega
        rcases ih (σ mover head tail).1
            (by simpa [children] using (σ mover head tail).2)
            (subhistory.snoc (σ mover head tail)) subfuel hchildSize with
          ⟨payoff, hendpoint, hpayoff⟩
        refine ⟨payoff, hendpoint, ?_⟩
        simpa using hpayoff
  · exact hsize

/-- Stopped execution of a translated global strategy reaches the same leaf
payoff as `GameTree.outcome`. -/
theorem stoppedHistory_strategy_reaches_outcome
    (root : GameTree N U) (σ : Strategy N U) :
    ∃ payoff : N → U,
      ((toExtensiveGame root).toArena.stoppedHistory
        (strategyHistoryPolicy root σ) root.size).1 = .Leaf payoff ∧
      payoff = outcome σ root := by
  simpa [Arena.stoppedHistory] using
    stoppedHistoryFrom_policy_reaches_outcome root σ
      (strategyHistoryPolicy root σ)
      (strategyHistoryPolicy_node root σ)
      root (Arena.History.nil) root.size (Nat.le_refl _)

/-- The stopped payoff of a translated global strategy is exactly the old
`GameTree.outcome`. -/
theorem stoppedPayoff_strategy_eq_outcome
    (root : GameTree N U) (σ : Strategy N U) :
    @ExtensiveGame.ObservedGame.stoppedPayoff N U
        (toObservedGame root) (toExtensiveGame_terminalDecidable root)
        (strategyToObservedProfile root σ)
        (toExtensiveGame_noChance root) root.size =
      some (outcome σ root) := by
  obtain ⟨payoff, hendpoint, hpayoff⟩ :=
    stoppedHistory_strategy_reaches_outcome root σ
  have hterminal :
      (toExtensiveGame root).isTerminal
        ((toExtensiveGame root).toArena.stoppedHistory
          (strategyHistoryPolicy root σ) root.size).1 := by
    rw [hendpoint]
    exact toExtensiveGame_isTerminal_leaf root payoff
  change
    (toExtensiveGame root).stoppedPayoff
        (strategyHistoryPolicy root σ) root.size =
      some (outcome σ root)
  rw [ExtensiveGame.stoppedPayoff_eq_some_of_terminal
    (toExtensiveGame root) (strategyHistoryPolicy root σ)
    root.size hterminal]
  apply congrArg some
  calc
    (toExtensiveGame root).payoff
        ((toExtensiveGame root).toArena.stoppedHistory
          (strategyHistoryPolicy root σ) root.size).1 =
        (toExtensiveGame root).payoff (.Leaf payoff) :=
      congrArg (toExtensiveGame root).payoff hendpoint
    _ = payoff := toExtensiveGame_payoff_leaf root payoff
    _ = outcome σ root := hpayoff

/-- Stopped execution of a translated strategic-form player profile agrees
with the outcome of `GameTree.profileStrategy`. -/
theorem stoppedPayoff_playerProfile_eq_outcome
    (root : GameTree N U) (σ : N → PlayerStrategy N U) :
    @ExtensiveGame.ObservedGame.stoppedPayoff N U
        (toObservedGame root) (toExtensiveGame_terminalDecidable root)
        (playerProfileToObservedProfile root σ)
        (toExtensiveGame_noChance root) root.size =
      some (outcome (profileStrategy σ) root) := by
  have hreaches :
      ∃ payoff : N → U,
        ((toExtensiveGame root).toArena.stoppedHistory
          (playerProfileHistoryPolicy root σ) root.size).1 =
            .Leaf payoff ∧
        payoff = outcome (profileStrategy σ) root := by
    simpa [Arena.stoppedHistory] using
      stoppedHistoryFrom_policy_reaches_outcome root (profileStrategy σ)
        (playerProfileHistoryPolicy root σ)
        (playerProfileHistoryPolicy_node root σ)
        root (Arena.History.nil) root.size (Nat.le_refl _)
  obtain ⟨payoff, hendpoint, hpayoff⟩ := hreaches
  have hterminal :
      (toExtensiveGame root).isTerminal
        ((toExtensiveGame root).toArena.stoppedHistory
          (playerProfileHistoryPolicy root σ) root.size).1 := by
    rw [hendpoint]
    exact toExtensiveGame_isTerminal_leaf root payoff
  change
    (toExtensiveGame root).stoppedPayoff
        (playerProfileHistoryPolicy root σ) root.size =
      some (outcome (profileStrategy σ) root)
  rw [ExtensiveGame.stoppedPayoff_eq_some_of_terminal
    (toExtensiveGame root) (playerProfileHistoryPolicy root σ)
    root.size hterminal]
  apply congrArg some
  calc
    (toExtensiveGame root).payoff
        ((toExtensiveGame root).toArena.stoppedHistory
          (playerProfileHistoryPolicy root σ) root.size).1 =
        (toExtensiveGame root).payoff (.Leaf payoff) :=
      congrArg (toExtensiveGame root).payoff hendpoint
    _ = payoff := toExtensiveGame_payoff_leaf root payoff
    _ = outcome (profileStrategy σ) root := hpayoff

/-! ### Representation-neutral game-form isomorphism -/

/-- The existing `GameTree` strategic semantics as a deterministic
strategy/outcome game form. -/
noncomputable def toGameForm (root : GameTree N U) : GameForm N where
  Strategy := fun _ => PlayerStrategy N U
  Outcome := N → U
  outcome σ := outcome (profileStrategy σ) root

/-- Convert an arbitrary observed pure profile back to the existing
player-strategy profile. -/
def observedProfileToPlayerProfile (root : GameTree N U)
    (σ : (toObservedGame root).PureProfile) :
    N → PlayerStrategy N U :=
  fun i => playerStrategyEquiv root i (σ i)

@[simp]
theorem observedProfileToPlayerProfile_toObserved
    (root : GameTree N U) (σ : N → PlayerStrategy N U) :
    observedProfileToPlayerProfile root
      (playerProfileToObservedProfile root σ) = σ := by
  funext i mover head tail
  rfl

@[simp]
theorem playerProfileToObservedProfile_toPlayer
    (root : GameTree N U)
    (σ : (toObservedGame root).PureProfile) :
    playerProfileToObservedProfile root
      (observedProfileToPlayerProfile root σ) = σ := by
  funext i info
  cases info
  rfl

/-! ### Termination-certified continuation semantics -/

/-- From any accumulated compiled history, an arbitrary observed pure profile
reaches the same leaf as the corresponding `GameTree` player profile whenever
the fuel dominates the current subtree size. -/
theorem stoppedHistoryFrom_observedProfile_reaches_outcome
    (root : GameTree N U)
    (profile : (toObservedGame root).PureProfile)
    (current :
      (toExtensiveGame root).toArena.HistoryFrom root)
    (fuel : ℕ) (hsize : current.1.size ≤ fuel) :
    ∃ payoff : N → U,
      ((toObservedGame root).stoppedHistoryFrom profile
        (toExtensiveGame_noChance root) current fuel).1 =
          GameTree.Leaf payoff ∧
      payoff =
        outcome
          (profileStrategy
            (observedProfileToPlayerProfile root profile))
          current.1 := by
  rw [← playerProfileToObservedProfile_toPlayer root profile]
  simpa [ExtensiveGame.ObservedGame.stoppedHistoryFrom] using
    stoppedHistoryFrom_policy_reaches_outcome root
      (profileStrategy
        (observedProfileToPlayerProfile root profile))
      (playerProfileHistoryPolicy root
        (observedProfileToPlayerProfile root profile))
      (playerProfileHistoryPolicy_node root
        (observedProfileToPlayerProfile root profile))
      current.1 current.2 fuel hsize

/-- The finite compiled `GameTree` terminates under every pure profile from
every admissible history root. -/
theorem toObservedGame_pureTerminatingOnAllContinuations
    (root : GameTree N U) :
    (toObservedGame root).PureTerminatingOnRoots
      (toExtensiveGame_noChance root)
      (ExtensiveGame.ObservedGame.ContinuationRootPresentation.allHistories
        (toObservedGame root).base) := by
  intro current _hroot profile
  refine ⟨root.size, ?_⟩
  obtain ⟨payoff, hendpoint, _⟩ :=
    stoppedHistoryFrom_observedProfile_reaches_outcome
      root profile current root.size
        (arenaHistory_subtree current.2).size_le
  rw [hendpoint]
  exact toExtensiveGame_isTerminal_leaf root payoff

/-- The total termination-certified payoff from an arbitrary compiled history
is the ordinary `GameTree.outcome` at its endpoint subtree. -/
theorem terminalPayoffFrom_observedProfile_eq_outcome
    (root : GameTree N U)
    (profile : (toObservedGame root).PureProfile)
    (current :
      (toExtensiveGame root).toArena.HistoryFrom root)
    (hterminates :
      (toObservedGame root).PureTerminatesFrom profile
        (toExtensiveGame_noChance root) current) :
    (toObservedGame root).terminalPayoffFrom profile
        (toExtensiveGame_noChance root) current hterminates =
      outcome
        (profileStrategy
          (observedProfileToPlayerProfile root profile))
        current.1 := by
  obtain ⟨payoff, hendpoint, hpayoff⟩ :=
    stoppedHistoryFrom_observedProfile_reaches_outcome
      root profile current root.size
        (arenaHistory_subtree current.2).size_le
  have hterminal :
      (toExtensiveGame root).isTerminal
        ((toObservedGame root).stoppedHistoryFrom profile
          (toExtensiveGame_noChance root) current root.size).1 := by
    rw [hendpoint]
    exact toExtensiveGame_isTerminal_leaf root payoff
  rw [ExtensiveGame.ObservedGame.terminalPayoffFrom,
    (toObservedGame root).terminalHistoryFrom_eq_of_terminal
      profile (toExtensiveGame_noChance root) current
      hterminates root.size hterminal]
  calc
    (toExtensiveGame root).payoff
        ((toObservedGame root).stoppedHistoryFrom profile
          (toExtensiveGame_noChance root) current root.size).1 =
        (toExtensiveGame root).payoff (.Leaf payoff) :=
      congrArg (toExtensiveGame root).payoff hendpoint
    _ = payoff := toExtensiveGame_payoff_leaf root payoff
    _ = outcome
          (profileStrategy
            (observedProfileToPlayerProfile root profile))
          current.1 := hpayoff

/-- At every compiled history, the existing `GameTree` game form is strictly
isomorphic to the termination-certified observed continuation game form. -/
noncomputable def terminalContinuationGameFormIso
    (root : GameTree N U)
    (current :
      (toExtensiveGame root).toArena.HistoryFrom root) :
    (toGameForm current.1).Iso
      ((toObservedGame root).terminalContinuationGameForm
        (toExtensiveGame_noChance root) current
        ((toObservedGame_pureTerminatingOnAllContinuations root)
          current trivial)) where
  strategyEquiv := fun i => (playerStrategyEquiv root i).symm
  outcomeEquiv := Equiv.refl _
  map_outcome := by
    intro profile
    change
      outcome (profileStrategy profile) current.1 =
        (toObservedGame root).terminalPayoffFrom
          (playerProfileToObservedProfile root profile)
          (toExtensiveGame_noChance root) current _
    rw [terminalPayoffFrom_observedProfile_eq_outcome,
      observedProfileToPlayerProfile_toObserved]

/-- The history-local total game-form isomorphism preserves terminal payoff
utilities. -/
theorem terminalContinuationGameFormIso_utilityCompatible
    (root : GameTree N U)
    (current :
      (toExtensiveGame root).toArena.HistoryFrom root) :
    (terminalContinuationGameFormIso root current).UtilityCompatible
      (fun payoff : N → U => payoff)
      (fun payoff : N → U => payoff) := by
  intro payoff i
  rfl

/-- Pure Nash equilibrium in a termination-certified observed continuation is
exactly the existing `GameTree.IsNashAt` predicate at the endpoint subtree. -/
theorem terminalContinuationGameForm_isNash_iff_isNashAt
    [DecidableEq N] [TotalPreorder U]
    (root : GameTree N U)
    (profile : N → PlayerStrategy N U)
    (current :
      (toExtensiveGame root).toArena.HistoryFrom root) :
    ((toObservedGame root).terminalContinuationGameForm
        (toExtensiveGame_noChance root) current
        ((toObservedGame_pureTerminatingOnAllContinuations root)
          current trivial)).IsNash
        (fun payoff : N → U => payoff)
        (playerProfileToObservedProfile root profile) ↔
      IsNashAt (profileStrategy profile) current.1 := by
  calc
    ((toObservedGame root).terminalContinuationGameForm
        (toExtensiveGame_noChance root) current
        ((toObservedGame_pureTerminatingOnAllContinuations root)
          current trivial)).IsNash
        (fun payoff : N → U => payoff)
        (playerProfileToObservedProfile root profile) ↔
        (toGameForm current.1).IsNash
          (fun payoff : N → U => payoff) profile := by
      simpa [GameForm.Iso.mapProfile,
        terminalContinuationGameFormIso] using
        ((terminalContinuationGameFormIso root current).isNash_iff
          (terminalContinuationGameFormIso_utilityCompatible
            root current) profile).symm
    _ ↔ IsNashAt (profileStrategy profile) current.1 := by
      change
        _root_.IsNashEquilibrium
            (GameTree.toStrategicGame current.1) profile ↔
          IsNashAt (profileStrategy profile) current.1
      exact toStrategicGame_nash_iff_isNashAt current.1 profile

/-- The endpoint compiler's termination-certified Nash-on-designated-
continuations predicate recovers the existing root-scoped structural
`GameTree.IsGlobalEndpointSubgamePerfectOn` predicate.

This is not the canonical occurrence-sensitive standard-SPE theorem. -/
theorem observed_isPureNashOnAllContinuations_iff_isGlobalEndpointSubgamePerfectOn
    [DecidableEq N] [TotalPreorder U]
    (root : GameTree N U)
    (profile : N → PlayerStrategy N U) :
    (toObservedGame root).IsPureNashOnRoots
        (toExtensiveGame_noChance root)
        (ExtensiveGame.ObservedGame.ContinuationRootPresentation.allHistories
          (toObservedGame root).base)
        (toObservedGame_pureTerminatingOnAllContinuations root)
        (fun payoff : N → U => payoff)
        (playerProfileToObservedProfile root profile) ↔
      IsGlobalEndpointSubgamePerfectOn (profileStrategy profile) root := by
  constructor
  · intro hspe subtree hsubtree
    let history := hsubtree.toArenaHistory
    have hobserved :=
      hspe ⟨subtree, history⟩ trivial
    exact
      (terminalContinuationGameForm_isNash_iff_isNashAt
        root profile ⟨subtree, history⟩).mp hobserved
  · intro hspe current _hroot
    have hsubtree : Subtree current.1 root :=
      arenaHistory_subtree current.2
    have htree := hspe current.1 hsubtree
    exact
      (terminalContinuationGameForm_isNash_iff_isNashAt
        root profile current).mpr htree

/-- The observed compilation's deterministic game form.

Its total outcome evaluator is justified operationally by
`stoppedPayoff_observedProfile_eq_gameFormOutcome` below. -/
noncomputable def observedToGameForm (root : GameTree N U) : GameForm N where
  Strategy := (toObservedGame root).PureStrategy
  Outcome := N → U
  outcome σ :=
    outcome (profileStrategy
      (observedProfileToPlayerProfile root σ)) root

/-- The old player-strategy semantics and the observed-game pure-strategy
semantics are isomorphic as deterministic game forms. -/
def gameFormIso (root : GameTree N U) :
    (toGameForm root).Iso (observedToGameForm root) where
  strategyEquiv := fun i => (playerStrategyEquiv root i).symm
  outcomeEquiv := Equiv.refl _
  map_outcome := by
    intro σ
    change outcome (profileStrategy σ) root =
      outcome
        (profileStrategy
          (observedProfileToPlayerProfile root
            (playerProfileToObservedProfile root σ))) root
    rw [observedProfileToPlayerProfile_toObserved]

/-- The observed game-form evaluator is exactly the payoff produced by
terminal-aware stopped execution. -/
theorem stoppedPayoff_observedProfile_eq_gameFormOutcome
    (root : GameTree N U)
    (σ : (toObservedGame root).PureProfile) :
    @ExtensiveGame.ObservedGame.stoppedPayoff N U
        (toObservedGame root) (toExtensiveGame_terminalDecidable root)
        σ (toExtensiveGame_noChance root) root.size =
      some ((observedToGameForm root).outcome σ) := by
  rw [← playerProfileToObservedProfile_toPlayer root σ]
  exact stoppedPayoff_playerProfile_eq_outcome root
    (observedProfileToPlayerProfile root σ)

/-- The game-form isomorphism preserves the identity utility interpretation of
terminal payoff vectors. -/
theorem gameFormIso_utilityCompatible (root : GameTree N U) :
    (gameFormIso root).UtilityCompatible
      (fun payoff : N → U => payoff)
      (fun payoff : N → U => payoff) := by
  intro payoff i
  rfl

/-- Pure Nash equilibrium is invariant under the `GameTree` to observed-game
strategy isomorphism. -/
theorem gameFormIso_isNash_iff
    [DecidableEq N] [Preorder U]
    (root : GameTree N U) (σ : (toGameForm root).Profile) :
    (toGameForm root).IsNash
        (fun payoff : N → U => payoff) σ ↔
      (observedToGameForm root).IsNash
        (fun payoff : N → U => payoff)
        (playerProfileToObservedProfile root σ) := by
  simpa [GameForm.Iso.mapProfile, gameFormIso] using
    (gameFormIso root).isNash_iff
      (gameFormIso_utilityCompatible root) σ

/-- The `GameTree` game-form Nash predicate is definitionally the existing
strategic-form Nash predicate. -/
theorem toGameForm_isNash_iff_toStrategicGame
    [DecidableEq N] [Preorder U]
    (root : GameTree N U) (σ : (toGameForm root).Profile) :
    (toGameForm root).IsNash
        (fun payoff : N → U => payoff) σ ↔
      _root_.IsNashEquilibrium (GameTree.toStrategicGame root) σ :=
  Iff.rfl

/-- Observed-game pure Nash is exactly the existing root-scoped
`GameTree.IsNashAt` predicate under the strategy isomorphism. -/
theorem observedGameForm_isNash_iff_isNashAt
    [DecidableEq N] [TotalPreorder U]
    (root : GameTree N U) (σ : N → PlayerStrategy N U) :
    (observedToGameForm root).IsNash
        (fun payoff : N → U => payoff)
        (playerProfileToObservedProfile root σ) ↔
      IsNashAt (profileStrategy σ) root := by
  calc
    (observedToGameForm root).IsNash
        (fun payoff : N → U => payoff)
        (playerProfileToObservedProfile root σ) ↔
        (toGameForm root).IsNash
          (fun payoff : N → U => payoff) σ :=
      (gameFormIso_isNash_iff root σ).symm
    _ ↔ IsNashAt (profileStrategy σ) root := by
      change
        _root_.IsNashEquilibrium (GameTree.toStrategicGame root) σ ↔
          IsNashAt (profileStrategy σ) root
      exact toStrategicGame_nash_iff_isNashAt root σ

end GameTree
