/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Observed.Morphism.Inverse

/-!
# EconCSLib.GameTheory.ExtensiveGame.Observed.PerfectRecall

Perfect recall for history-indexed observed extensive games.

For a player `i`, a personal decision records the decision information state
previously encountered by `i` together with the abstract information action
chosen there.  `ownDecisionHistory` extracts the ordered list of those records
from a complete game history, ignoring chance moves and moves of other
players.

Player `i` has perfect recall when two current decision histories in the same
information state have identical personal decision histories.  Thus the
player never forgets either what they previously knew or which abstract action
they chose.  The definition imposes no finiteness, chance, or termination
assumption.

A strict `ObservedGame.Iso` maps personal decision histories pointwise through
the information-state/action equivalences.  It therefore preserves and
reflects perfect recall, allowing this structural hypothesis to be proved in
whichever EFG representation is most convenient.

## Main definitions

* `ObservedGame.PersonalDecision` — one remembered information/action pair.
* `ObservedGame.ownDecisionHistory` — a player's remembered decision sequence.
* `ObservedGame.HasPerfectRecall` — perfect recall for one player.
* `ObservedGame.HasNoAbsentMindedness` — the same decision information state
  cannot recur after the player has acted.
* `ObservedGame.HasSingletonInformation` and `PerfectInformation` —
  history-indexed perfect information.
* `ObservedGame.PerfectRecall` — perfect recall for every player.
* `ObservedGame.RecallCertificate` — factorization of remembered personal
  decisions through the current information state.

## Main results

* `ObservedGame.Iso.map_ownDecisionHistory` — strict naturality of remembered
  decision sequences.
* `HasPerfectRecall.hasNoAbsentMindedness` — perfect recall rules out repeated
  queries to one information state along a play.
* `ObservedGame.Iso.hasPerfectRecall_iff` and `perfectRecall_iff` — two-way
  structural transfer.
* `recallCertificate_nonempty_iff_perfectRecall` — certificate
  characterization of perfect recall.
* `ObservedGame.Iso.recallCertificate_nonempty_iff` — strict transfer of
  compiler recall certificates.
-/

namespace ExtensiveGame.ObservedGame

variable {N U : Type*}

/-- One of player `i`'s past decisions, packaged as the information state they
encountered and the abstract action they chose there. -/
abbrev PersonalDecision (G : ObservedGame N U) (i : N) :=
  Σ information : G.InfoState i, G.InfoAction i information

/-- Package the information state and abstract information action represented
by a concrete action at a player-controlled complete history. -/
def personalDecisionAt (G : ObservedGame N U) (i : N)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (hmover : G.base.mover history.1 = some i)
    (action : G.base.Action history.1) :
    G.PersonalDecision i :=
  ⟨G.infoAt history i hmover,
    (G.actionEquiv history i hmover).symm action⟩

/-- The ordered sequence of information states and own actions along a typed
path.  This path-indexed worker exposes structural recursion cleanly. -/
def ownDecisionHistoryPath [DecidableEq N]
    (G : ObservedGame N U) (i : N) :
    {state : G.base.State} →
      G.base.toArena.History G.base.init state →
        List (G.PersonalDecision i)
  | _, .nil => []
  | _, @Arena.History.snoc _ _ state path action =>
      let previous :
          G.base.toArena.HistoryFrom G.base.init :=
        ⟨state, path⟩
      if hmover : G.base.mover state = some i then
        G.ownDecisionHistoryPath i path ++
          [G.personalDecisionAt i previous hmover action]
      else
        G.ownDecisionHistoryPath i path

/-- The ordered sequence of information states and own actions previously
encountered by player `i` along a complete history.

The endpoint itself has not yet acted, so a history ending at a decision node
contains precisely the player's decisions strictly before that node. -/
def ownDecisionHistory [DecidableEq N]
    (G : ObservedGame N U) (i : N)
    (history : G.base.toArena.HistoryFrom G.base.init) :
    List (G.PersonalDecision i) :=
  G.ownDecisionHistoryPath i history.2

/-- A concrete occurrence of one personal decision inside a complete
history.  The path is decomposed into the prefix ending at the decision, the
chosen action, and the suffix after that action. -/
structure PersonalDecisionOccurrence
    (G : ObservedGame N U) (i : N)
    (history :
      G.base.toArena.HistoryFrom G.base.init)
    (decision : G.PersonalDecision i) where
  /-- State at which the recorded decision occurred. -/
  state : G.base.State
  /-- Complete path prefix ending at the decision state. -/
  before :
    G.base.toArena.History G.base.init state
  /-- Player `i` controlled the decision state. -/
  mover :
    G.base.mover state = some i
  /-- Concrete action chosen at the occurrence. -/
  action :
    G.base.Action state
  /-- Remaining path after the recorded action. -/
  after :
    G.base.toArena.History
      (G.base.next state action) history.1
  /-- The occurrence decomposition reconstructs the complete path. -/
  path_eq :
    (before.snoc action).append after =
      history.2
  /-- The packaged information/action record is the requested decision. -/
  decision_eq :
    G.personalDecisionAt
        i ⟨state, before⟩ mover action =
      decision

/-- Every member of an extracted own-decision history has a concrete
path occurrence witnessing it. -/
theorem exists_personalDecisionOccurrence_of_mem
    [DecidableEq N]
    (G : ObservedGame N U) (i : N)
    (history :
      G.base.toArena.HistoryFrom G.base.init)
    (decision : G.PersonalDecision i)
    (hmem :
      decision ∈
        G.ownDecisionHistory i history) :
    Nonempty
      (G.PersonalDecisionOccurrence
        i history decision) := by
  obtain ⟨finish, path⟩ := history
  induction path with
  | nil =>
      simp [ownDecisionHistory,
        ownDecisionHistoryPath] at hmem
  | @snoc state path action ih =>
      let previous :
          G.base.toArena.HistoryFrom
            G.base.init :=
        ⟨state, path⟩
      by_cases hmover :
          G.base.mover state = some i
      · simp [ownDecisionHistory,
          ownDecisionHistoryPath, hmover]
          at hmem
        rcases hmem with
          hprevious | hcurrent
        · obtain ⟨occurrence⟩ :=
            ih hprevious
          exact
            ⟨{
              state := occurrence.state
              before := occurrence.before
              mover := occurrence.mover
              action := occurrence.action
              after :=
                occurrence.after.snoc action
              path_eq := by
                rw [Arena.History.append_snoc,
                  occurrence.path_eq]
              decision_eq :=
                occurrence.decision_eq
            }⟩
        · have hdecision :
              G.personalDecisionAt
                  i previous hmover action =
                decision := by
            exact hcurrent.symm
          exact
            ⟨{
              state := state
              before := path
              mover := hmover
              action := action
              after := Arena.History.nil
              path_eq := by
                simp
              decision_eq := hdecision
            }⟩
      · simp [ownDecisionHistory,
          ownDecisionHistoryPath, hmover]
          at hmem
        obtain ⟨occurrence⟩ :=
          ih hmem
        exact
          ⟨{
            state := occurrence.state
            before := occurrence.before
            mover := occurrence.mover
            action := occurrence.action
            after :=
              occurrence.after.snoc action
            path_eq := by
              rw [Arena.History.append_snoc,
                occurrence.path_eq]
            decision_eq :=
              occurrence.decision_eq
          }⟩

@[simp]
theorem ownDecisionHistory_nil [DecidableEq N]
    (G : ObservedGame N U) (i : N) :
    G.ownDecisionHistory i
        (Arena.HistoryFrom.nil G.base.toArena G.base.init) =
      [] := by
  rfl

@[simp]
theorem ownDecisionHistory_snoc_of_mover [DecidableEq N]
    (G : ObservedGame N U) (i : N)
    {state : G.base.State}
    (path : G.base.toArena.History G.base.init state)
    (action : G.base.Action state)
    (hmover : G.base.mover state = some i) :
    G.ownDecisionHistory i
        ⟨G.base.next state action, path.snoc action⟩ =
      G.ownDecisionHistory i ⟨state, path⟩ ++
        [G.personalDecisionAt i ⟨state, path⟩ hmover action] := by
  simp [ownDecisionHistory, ownDecisionHistoryPath, hmover]

@[simp]
theorem ownDecisionHistory_snoc_of_not_mover [DecidableEq N]
    (G : ObservedGame N U) (i : N)
    {state : G.base.State}
    (path : G.base.toArena.History G.base.init state)
    (action : G.base.Action state)
    (hmover : G.base.mover state ≠ some i) :
    G.ownDecisionHistory i
        ⟨G.base.next state action, path.snoc action⟩ =
      G.ownDecisionHistory i ⟨state, path⟩ := by
  simp [ownDecisionHistory, ownDecisionHistoryPath, hmover]

/-- Extending a complete history cannot shorten a player's personal decision
history. -/
theorem ownDecisionHistory_length_le_append
    [DecidableEq N]
    (G : ObservedGame N U) (i : N)
    {middle finish : G.base.State}
    (basePath :
      G.base.toArena.History G.base.init middle)
    (suffix :
      G.base.toArena.History middle finish) :
    (G.ownDecisionHistory i
        ⟨middle, basePath⟩).length ≤
      (G.ownDecisionHistory i
        ⟨finish, basePath.append suffix⟩).length := by
  induction suffix with
  | nil =>
      simp
  | @snoc state suffix action ih =>
      by_cases hmover :
          G.base.mover state = some i
      · rw [Arena.History.append_snoc]
        rw [G.ownDecisionHistory_snoc_of_mover
          i (basePath.append suffix) action hmover]
        simp only [List.length_append, List.length_cons,
          List.length_nil]
        omega
      · rw [Arena.History.append_snoc]
        rw [G.ownDecisionHistory_snoc_of_not_mover
          i (basePath.append suffix) action hmover]
        exact ih

/-- A continuation extends, rather than rewrites, every player's personal
decision history.

This prefix form is stronger than the corresponding length inequality and is
the structural fact needed to remove the pre-continuation part of a recall
certificate when behavioralizing a mixed plan at an arbitrary root. -/
theorem ownDecisionHistory_prefix_append
    [DecidableEq N]
    (G : ObservedGame N U) (i : N)
    {middle finish : G.base.State}
    (basePath :
      G.base.toArena.History G.base.init middle)
    (suffix :
      G.base.toArena.History middle finish) :
    G.ownDecisionHistory i
        ⟨middle, basePath⟩ <+:
      G.ownDecisionHistory i
        ⟨finish, basePath.append suffix⟩ := by
  induction suffix with
  | nil =>
      exact List.prefix_refl _
  | @snoc state suffix action ih =>
      rw [Arena.History.append_snoc]
      by_cases hmover :
          G.base.mover state = some i
      · rw [G.ownDecisionHistory_snoc_of_mover
          i (basePath.append suffix) action hmover]
        exact ih.trans (List.prefix_append _ _)
      · rw [G.ownDecisionHistory_snoc_of_not_mover
          i (basePath.append suffix) action hmover]
        exact ih

/-- Player `i` has perfect recall when equal current decision information
states imply equal sequences of the information states and own actions that
the player previously encountered. -/
def HasPerfectRecall [DecidableEq N]
    (G : ObservedGame N U) (i : N) : Prop :=
  ∀ (first second :
      G.base.toArena.HistoryFrom G.base.init)
    (hfirst : G.base.mover first.1 = some i)
    (hsecond : G.base.mover second.1 = some i),
    G.infoAt first i hfirst = G.infoAt second i hsecond →
      G.ownDecisionHistory i first =
        G.ownDecisionHistory i second

/-- Player `i` has singleton decision information when equal decision
information states force equality of the complete histories themselves.

This is the history-indexed perfect-information condition for one player. -/
def HasSingletonInformation
    (G : ObservedGame N U) (i : N) : Prop :=
  ∀ (first second :
      G.base.toArena.HistoryFrom G.base.init)
    (hfirst : G.base.mover first.1 = some i)
    (hsecond : G.base.mover second.1 = some i),
    G.infoAt first i hfirst = G.infoAt second i hsecond →
      first = second

/-- Singleton decision information implies perfect recall. -/
theorem HasSingletonInformation.hasPerfectRecall
    [DecidableEq N]
    {G : ObservedGame N U} {i : N}
    (hinformation : G.HasSingletonInformation i) :
    G.HasPerfectRecall i := by
  intro first second hfirst hsecond hsame
  exact congrArg
    (G.ownDecisionHistory i)
    (hinformation first second hfirst hsecond hsame)

/-- Every player has singleton decision information. -/
def PerfectInformation (G : ObservedGame N U) : Prop :=
  ∀ i : N, G.HasSingletonInformation i

/-- Every player has perfect recall. -/
def PerfectRecall [DecidableEq N]
    (G : ObservedGame N U) : Prop :=
  ∀ i : N, G.HasPerfectRecall i

/-- Player `i` is never asked to act twice at the same decision information
state along one complete history.

The second occurrence is presented by a suffix beginning after the first
occurrence's action.  This is precisely the no-repeated-key condition needed
to compare on-demand behavioral randomization with a pre-sampled pure-plan
table. -/
def HasNoAbsentMindedness
    (G : ObservedGame N U) (i : N) : Prop :=
  ∀ (first :
      G.base.toArena.HistoryFrom G.base.init)
    (hfirst :
      G.base.mover first.1 = some i)
    (action : G.base.Action first.1)
    (finish : G.base.State)
    (suffix :
      G.base.toArena.History
        (G.base.next first.1 action) finish)
    (hsecond :
      G.base.mover finish = some i),
    G.infoAt first i hfirst ≠
      G.infoAt
        ⟨finish,
          (first.2.snoc action).append suffix⟩
        i hsecond

/-- Under no absent-mindedness, every previously recorded own decision has an
information state different from the player's current information state. -/
theorem HasNoAbsentMindedness.info_ne_of_mem_ownDecisionHistory
    [DecidableEq N]
    {G : ObservedGame N U} {i : N}
    (hnoAbsent : G.HasNoAbsentMindedness i)
    (history :
      G.base.toArena.HistoryFrom G.base.init)
    (hmover :
      G.base.mover history.1 = some i)
    (decision : G.PersonalDecision i)
    (hmem :
      decision ∈
        G.ownDecisionHistory i history) :
    decision.1 ≠
      G.infoAt history i hmover := by
  obtain ⟨occurrence⟩ :=
    G.exists_personalDecisionOccurrence_of_mem
      i history decision hmem
  have hdistinct :=
    hnoAbsent
      ⟨occurrence.state, occurrence.before⟩
      occurrence.mover occurrence.action
      history.1 occurrence.after hmover
  rw [occurrence.path_eq] at hdistinct
  have hfirst :
      G.infoAt
          ⟨occurrence.state, occurrence.before⟩
          i occurrence.mover =
        decision.1 :=
    congrArg Sigma.fst occurrence.decision_eq
  intro hequal
  apply hdistinct
  exact hfirst.trans hequal

/-- No player is absent-minded. -/
def NoAbsentMindedness
    (G : ObservedGame N U) : Prop :=
  ∀ i : N, G.HasNoAbsentMindedness i

/-- Perfect recall rules out absent-mindedness.

After the first decision, the player's personal decision-history length has
strictly increased and can never decrease along a suffix.  Equal information
states would force those histories to be equal by perfect recall, a
contradiction. -/
theorem HasPerfectRecall.hasNoAbsentMindedness
    [DecidableEq N]
    {G : ObservedGame N U} {i : N}
    (hrecall : G.HasPerfectRecall i) :
    G.HasNoAbsentMindedness i := by
  intro first hfirst action finish suffix hsecond
    hsame
  let afterFirst :
      G.base.toArena.HistoryFrom G.base.init :=
    ⟨G.base.next first.1 action,
      first.2.snoc action⟩
  let second :
      G.base.toArena.HistoryFrom G.base.init :=
    ⟨finish,
      (first.2.snoc action).append suffix⟩
  have hstrict :
      (G.ownDecisionHistory i first).length <
        (G.ownDecisionHistory i second).length := by
    have hstep :
        G.ownDecisionHistory i afterFirst =
          G.ownDecisionHistory i first ++
            [G.personalDecisionAt
              i first hfirst action] := by
      exact
        G.ownDecisionHistory_snoc_of_mover
          i first.2 action hfirst
    have htail :
        (G.ownDecisionHistory i afterFirst).length ≤
          (G.ownDecisionHistory i second).length := by
      exact
        G.ownDecisionHistory_length_le_append
          i (first.2.snoc action) suffix
    rw [hstep] at htail
    simp only [List.length_append, List.length_cons,
      List.length_nil] at htail
    omega
  have hequal :
      G.ownDecisionHistory i first =
        G.ownDecisionHistory i second :=
    hrecall first second hfirst hsecond hsame
  rw [hequal] at hstrict
  exact (Nat.lt_irrefl _ hstrict)

/-- Perfect recall for every player implies global no-absent-mindedness. -/
theorem PerfectRecall.noAbsentMindedness
    [DecidableEq N]
    {G : ObservedGame N U}
    (hrecall : G.PerfectRecall) :
    G.NoAbsentMindedness :=
  fun i =>
    (hrecall i).hasNoAbsentMindedness

/-- Perfect information implies perfect recall. -/
theorem PerfectInformation.perfectRecall
    [DecidableEq N]
    {G : ObservedGame N U}
    (hinformation : G.PerfectInformation) :
    G.PerfectRecall :=
  fun i => (hinformation i).hasPerfectRecall

/-- A witness that each player's remembered personal-decision sequence factors
through the player's current decision information state.

This is a compiler-friendly presentation of perfect recall.  A concrete EFG
compiler may assign a canonical remembered sequence to each information state
and prove the single `remembered_infoAt` equation, rather than comparing every
pair of represented histories directly. -/
structure RecallCertificate [DecidableEq N]
    (G : ObservedGame N U) where
  /-- The personal-decision sequence remembered at an information state. -/
  remembered :
    (i : N) → G.InfoState i →
      List (G.PersonalDecision i)
  /-- At every represented player decision, the assigned sequence is exactly
  the sequence extracted from the complete history. -/
  remembered_infoAt :
    ∀ (i : N)
      (history : G.base.toArena.HistoryFrom G.base.init)
      (hmover : G.base.mover history.1 = some i),
      remembered i (G.infoAt history i hmover) =
        G.ownDecisionHistory i history

namespace RecallCertificate

/-- A recall factorization certificate proves perfect recall. -/
theorem perfectRecall [DecidableEq N]
    {G : ObservedGame N U}
    (certificate : G.RecallCertificate) :
    G.PerfectRecall := by
  intro i first second hfirst hsecond hsame
  rw [← certificate.remembered_infoAt i first hfirst]
  rw [← certificate.remembered_infoAt i second hsecond]
  rw [hsame]

end RecallCertificate

/-- A represented history witnessing that `information` is a reachable
decision information state for player `i`. -/
structure DecisionInfoWitness
    (G : ObservedGame N U) (i : N)
    (information : G.InfoState i) where
  /-- A complete history represented by the information state. -/
  history : G.base.toArena.HistoryFrom G.base.init
  /-- Player `i` controls the endpoint. -/
  mover : G.base.mover history.1 = some i
  /-- The endpoint has the specified information state. -/
  infoAt_eq : G.infoAt history i mover = information

/-- Perfect recall canonically yields a recall factorization certificate by
choosing one represented history for each reachable information state.
Unreachable information states may be assigned the empty sequence. -/
noncomputable def PerfectRecall.toRecallCertificate
    [DecidableEq N]
    {G : ObservedGame N U}
    (hrecall : G.PerfectRecall) :
    G.RecallCertificate where
  remembered := by
    classical
    exact fun i information =>
      if hexists :
          Nonempty (DecisionInfoWitness G i information) then
        G.ownDecisionHistory i
          (Classical.choice hexists).history
      else
        []
  remembered_infoAt := by
    intro i history hmover
    classical
    let witness :
        DecisionInfoWitness G i
          (G.infoAt history i hmover) :=
      ⟨history, hmover, rfl⟩
    have hexists :
        Nonempty
          (DecisionInfoWitness G i
            (G.infoAt history i hmover)) :=
      ⟨witness⟩
    rw [dif_pos hexists]
    exact
      hrecall i
        (Classical.choice hexists).history history
        (Classical.choice hexists).mover hmover
        (Classical.choice hexists).infoAt_eq

/-- Perfect recall holds exactly when a recall factorization certificate
exists. -/
theorem recallCertificate_nonempty_iff_perfectRecall
    [DecidableEq N]
    (G : ObservedGame N U) :
    Nonempty G.RecallCertificate ↔ G.PerfectRecall := by
  constructor
  · rintro ⟨certificate⟩
    exact certificate.perfectRecall
  · intro hrecall
    exact ⟨hrecall.toRecallCertificate⟩

end ExtensiveGame.ObservedGame

namespace ExtensiveGame.ObservedGame.Iso

variable {N U : Type*}
variable {G H : ObservedGame N U}

/-- A strict observed-EFG isomorphism maps a packaged personal decision through
the corresponding information-state and information-action equivalences. -/
def personalDecisionEquiv (e : G.Iso H) (i : N) :
    G.PersonalDecision i ≃ H.PersonalDecision i :=
  (e.infoStateEquiv i).sigmaCongr (e.infoActionEquiv i)

private theorem sigma_mk_cast_eq
    {α : Type*} {fiber : α → Type*}
    {first second : α} (hindex : first = second)
    (value : fiber first) :
    (⟨second, cast (congrArg fiber hindex) value⟩ :
        Σ index, fiber index) =
      ⟨first, value⟩ := by
  subst second
  rfl

/-- Mapping a concrete player decision through the strict history-action
equivalence agrees with mapping its packaged information/action record. -/
theorem map_personalDecisionAt
    (e : G.Iso H) (i : N)
    (history : G.base.toArena.HistoryFrom G.base.init)
    (hsource : G.base.mover history.1 = some i)
    (htarget :
      H.base.mover (e.historyIso.stateEquiv history).1 = some i)
    (action : G.base.Action history.1) :
    H.personalDecisionAt i
        (e.historyIso.stateEquiv history) htarget
        (e.historyIso.actionEquiv history action) =
      e.personalDecisionEquiv i
        (G.personalDecisionAt i history hsource action) := by
  let sourceInformation :=
    G.infoAt history i hsource
  let sourceAction :=
    (G.actionEquiv history i hsource).symm action
  have hinfo :
      e.infoStateEquiv i sourceInformation =
        H.infoAt (e.historyIso.stateEquiv history) i htarget :=
    e.map_infoAt history i hsource htarget
  let mappedAction :=
    e.infoActionEquiv i sourceInformation sourceAction
  let transportedAction :=
    cast
      (congrArg (H.InfoAction i) hinfo)
      mappedAction
  have haction :
      (H.actionEquiv
          (e.historyIso.stateEquiv history) i htarget).symm
          (e.historyIso.actionEquiv history action) =
        transportedAction := by
    apply
      (H.actionEquiv
        (e.historyIso.stateEquiv history) i htarget).injective
    rw [(H.actionEquiv
      (e.historyIso.stateEquiv history) i htarget).apply_symm_apply]
    simpa [sourceAction, sourceInformation, mappedAction,
      transportedAction] using
      (e.map_infoActionAt history i hsource htarget sourceAction).symm
  change
    (⟨H.infoAt
        (e.historyIso.stateEquiv history) i htarget,
      (H.actionEquiv
        (e.historyIso.stateEquiv history) i htarget).symm
        (e.historyIso.actionEquiv history action)⟩ :
      H.PersonalDecision i) =
    e.personalDecisionEquiv i
      (⟨sourceInformation, sourceAction⟩ :
        G.PersonalDecision i)
  rw [haction]
  change
    (⟨H.infoAt
        (e.historyIso.stateEquiv history) i htarget,
      transportedAction⟩ :
      H.PersonalDecision i) =
    ⟨e.infoStateEquiv i sourceInformation, mappedAction⟩
  exact sigma_mk_cast_eq hinfo mappedAction

/-- Strict history mapping sends a player's remembered decision sequence to
the pointwise-mapped source sequence. -/
theorem map_ownDecisionHistory [DecidableEq N]
    (e : G.Iso H) (i : N)
    (history : G.base.toArena.HistoryFrom G.base.init) :
    H.ownDecisionHistory i
        (e.historyIso.stateEquiv history) =
      (G.ownDecisionHistory i history).map
        (e.personalDecisionEquiv i) := by
  obtain ⟨state, path⟩ := history
  induction path with
  | nil =>
      change
        H.ownDecisionHistory i
            (e.historyIso.stateEquiv
              (Arena.HistoryFrom.nil
                G.base.toArena G.base.init)) =
          (G.ownDecisionHistory i
            (Arena.HistoryFrom.nil
              G.base.toArena G.base.init)).map
            (e.personalDecisionEquiv i)
      rw [e.map_init]
      rw [H.ownDecisionHistory_nil, G.ownDecisionHistory_nil]
      rfl
  | @snoc state path action ih =>
      let previous :
          G.base.toArena.HistoryFrom G.base.init :=
        ⟨state, path⟩
      change
        H.ownDecisionHistory i
            (e.historyIso.stateEquiv
              (G.base.unfold.toArena.next previous action)) =
          (G.ownDecisionHistory i
            (G.base.unfold.toArena.next previous action)).map
              (e.personalDecisionEquiv i)
      rw [e.historyIso.map_next previous action]
      change
        H.ownDecisionHistory i
            ⟨H.base.next
                (e.historyIso.stateEquiv previous).1
                (e.historyIso.actionEquiv previous action),
              (e.historyIso.stateEquiv previous).2.snoc
                (e.historyIso.actionEquiv previous action)⟩ =
          (G.ownDecisionHistory i
            ⟨G.base.next state action, path.snoc action⟩).map
              (e.personalDecisionEquiv i)
      by_cases hsource : G.base.mover state = some i
      · have htarget :
            H.base.mover
                (e.historyIso.stateEquiv previous).1 =
              some i := by
          rw [e.map_mover previous]
          exact hsource
        rw [H.ownDecisionHistory_snoc_of_mover
          i (e.historyIso.stateEquiv previous).2
          (e.historyIso.actionEquiv previous action)
          htarget]
        rw [G.ownDecisionHistory_snoc_of_mover
          i path action hsource]
        have ih' :
            H.ownDecisionHistory i
                ⟨(e.historyIso.stateEquiv previous).1,
                  (e.historyIso.stateEquiv previous).2⟩ =
              (G.ownDecisionHistory i ⟨state, path⟩).map
                (e.personalDecisionEquiv i) := by
          simpa [previous] using ih
        rw [List.map_append, ih', List.map_singleton]
        congr 1
        simpa [previous] using
          congrArg (fun decision => [decision])
            (e.map_personalDecisionAt
              i previous hsource htarget action)
      · have htarget :
            H.base.mover
                (e.historyIso.stateEquiv previous).1 ≠
              some i := by
          rw [e.map_mover previous]
          exact hsource
        rw [H.ownDecisionHistory_snoc_of_not_mover
          i (e.historyIso.stateEquiv previous).2
          (e.historyIso.actionEquiv previous action)
          htarget]
        rw [G.ownDecisionHistory_snoc_of_not_mover
          i path action hsource]
        exact ih

private theorem infoAt_eq_of_history_eq
    (K : ObservedGame N U) (i : N)
    {first second :
      K.base.toArena.HistoryFrom K.base.init}
    (hhistory : first = second)
    (hfirst : K.base.mover first.1 = some i)
    (hsecond : K.base.mover second.1 = some i) :
    K.infoAt first i hfirst =
      K.infoAt second i hsecond := by
  subst second
  rfl

/-- Strict observed-EFG isomorphisms preserve and reflect perfect recall for
one player. -/
theorem hasPerfectRecall_iff [DecidableEq N]
    (e : G.Iso H) (i : N) :
    G.HasPerfectRecall i ↔ H.HasPerfectRecall i := by
  constructor
  · intro hrecall targetFirst targetSecond
      htargetFirst htargetSecond hsame
    let sourceFirst :=
      e.historyIso.stateEquiv.symm targetFirst
    let sourceSecond :=
      e.historyIso.stateEquiv.symm targetSecond
    have hmapFirst :
        e.historyIso.stateEquiv sourceFirst = targetFirst :=
      e.historyIso.stateEquiv.apply_symm_apply targetFirst
    have hmapSecond :
        e.historyIso.stateEquiv sourceSecond = targetSecond :=
      e.historyIso.stateEquiv.apply_symm_apply targetSecond
    have hsourceFirst :
        G.base.mover sourceFirst.1 = some i := by
      have hmapped :
          H.base.mover
              (e.historyIso.stateEquiv sourceFirst).1 =
            some i := by
        simpa [hmapFirst] using htargetFirst
      rw [e.map_mover sourceFirst] at hmapped
      exact hmapped
    have hsourceSecond :
        G.base.mover sourceSecond.1 = some i := by
      have hmapped :
          H.base.mover
              (e.historyIso.stateEquiv sourceSecond).1 =
            some i := by
        simpa [hmapSecond] using htargetSecond
      rw [e.map_mover sourceSecond] at hmapped
      exact hmapped
    have hsourceInfo :
        G.infoAt sourceFirst i hsourceFirst =
          G.infoAt sourceSecond i hsourceSecond := by
      have hmappedFirst :
          H.base.mover
              (e.historyIso.stateEquiv sourceFirst).1 =
            some i := by
        rw [e.map_mover sourceFirst]
        exact hsourceFirst
      have hmappedSecond :
          H.base.mover
              (e.historyIso.stateEquiv sourceSecond).1 =
            some i := by
        rw [e.map_mover sourceSecond]
        exact hsourceSecond
      have hfirstInfo :
          H.infoAt
              (e.historyIso.stateEquiv sourceFirst)
              i hmappedFirst =
            H.infoAt targetFirst i htargetFirst :=
        infoAt_eq_of_history_eq H i hmapFirst
          hmappedFirst htargetFirst
      have hsecondInfo :
          H.infoAt
              (e.historyIso.stateEquiv sourceSecond)
              i hmappedSecond =
            H.infoAt targetSecond i htargetSecond :=
        infoAt_eq_of_history_eq H i hmapSecond
          hmappedSecond htargetSecond
      apply (e.infoStateEquiv i).injective
      calc
        e.infoStateEquiv i
            (G.infoAt sourceFirst i hsourceFirst) =
          H.infoAt
            (e.historyIso.stateEquiv sourceFirst)
            i hmappedFirst :=
            e.map_infoAt sourceFirst i
              hsourceFirst hmappedFirst
        _ = H.infoAt targetFirst i htargetFirst := by
              exact hfirstInfo
        _ = H.infoAt targetSecond i htargetSecond := hsame
        _ = H.infoAt
            (e.historyIso.stateEquiv sourceSecond)
            i hmappedSecond :=
              hsecondInfo.symm
        _ = e.infoStateEquiv i
            (G.infoAt sourceSecond i hsourceSecond) :=
              (e.map_infoAt sourceSecond i
                hsourceSecond hmappedSecond).symm
    have hsourceHistory :=
      hrecall sourceFirst sourceSecond
        hsourceFirst hsourceSecond hsourceInfo
    have hfirstMap :=
      e.map_ownDecisionHistory i sourceFirst
    have hsecondMap :=
      e.map_ownDecisionHistory i sourceSecond
    rw [hsourceHistory] at hfirstMap
    calc
      H.ownDecisionHistory i targetFirst =
          H.ownDecisionHistory i
            (e.historyIso.stateEquiv sourceFirst) := by
              rw [hmapFirst]
      _ = (G.ownDecisionHistory i sourceSecond).map
          (e.personalDecisionEquiv i) := hfirstMap
      _ = H.ownDecisionHistory i
          (e.historyIso.stateEquiv sourceSecond) :=
            hsecondMap.symm
      _ = H.ownDecisionHistory i targetSecond := by
            rw [hmapSecond]
  · intro hrecall sourceFirst sourceSecond
      hsourceFirst hsourceSecond hsame
    have htargetFirst :
        H.base.mover
            (e.historyIso.stateEquiv sourceFirst).1 =
          some i := by
      rw [e.map_mover sourceFirst]
      exact hsourceFirst
    have htargetSecond :
        H.base.mover
            (e.historyIso.stateEquiv sourceSecond).1 =
          some i := by
      rw [e.map_mover sourceSecond]
      exact hsourceSecond
    have htargetInfo :
        H.infoAt
            (e.historyIso.stateEquiv sourceFirst)
            i htargetFirst =
          H.infoAt
            (e.historyIso.stateEquiv sourceSecond)
            i htargetSecond := by
      rw [← e.map_infoAt sourceFirst i
        hsourceFirst htargetFirst]
      rw [← e.map_infoAt sourceSecond i
        hsourceSecond htargetSecond]
      exact congrArg (e.infoStateEquiv i) hsame
    have htargetHistory :=
      hrecall
        (e.historyIso.stateEquiv sourceFirst)
        (e.historyIso.stateEquiv sourceSecond)
        htargetFirst htargetSecond htargetInfo
    rw [e.map_ownDecisionHistory i sourceFirst,
      e.map_ownDecisionHistory i sourceSecond] at htargetHistory
    exact
      (e.personalDecisionEquiv i).injective.list_map
        htargetHistory

/-- Strict observed-EFG isomorphisms preserve and reflect perfect recall for
all players. -/
theorem perfectRecall_iff [DecidableEq N]
    (e : G.Iso H) :
    G.PerfectRecall ↔ H.PerfectRecall := by
  constructor <;> intro hrecall i
  · exact (e.hasPerfectRecall_iff i).mp (hrecall i)
  · exact (e.hasPerfectRecall_iff i).mpr (hrecall i)

/-- Existence of a compiler-style recall factorization certificate is
invariant under strict observed-EFG isomorphism. -/
theorem recallCertificate_nonempty_iff
    [DecidableEq N]
    (e : G.Iso H) :
    Nonempty G.RecallCertificate ↔
      Nonempty H.RecallCertificate := by
  rw [G.recallCertificate_nonempty_iff_perfectRecall]
  rw [H.recallCertificate_nonempty_iff_perfectRecall]
  exact e.perfectRecall_iff

end ExtensiveGame.ObservedGame.Iso
