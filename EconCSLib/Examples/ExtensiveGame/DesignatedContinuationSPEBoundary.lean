/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Compiler.GameTreeOccurrenceObserved

/-!
# EconCSLib.Examples.ExtensiveGame.DesignatedContinuationSPEBoundary

A finite regression separating Nash equilibrium on presentation-designated
continuations from standard subgame-perfect equilibrium.

Player `0` may quit for payoff `(0, 0)` or enter a player-`1` continuation.
The baseline profile quits and carries the incredible threat that player `1`
would choose `(−1, 0)` instead of `(1, 1)`.  It is Nash at the initial root,
but not Nash in the off-path continuation.

`rootOnlyObserved` deliberately designates only the initial history.  The
baseline therefore satisfies
`IsPureNashOnRoots`. A lawful `SubgameSystem`, however, is
structural and may include the off-path root independently of that presentation
metadata. The same endpoint plan lifted to the canonical occurrence compiler
is proved not to satisfy its complete all-history
`IsPureStandardSubgamePerfect` predicate. The occurrence presentation with
only the initial designated root separately proves that a canonical complete
system still exists but is not presentation-visible.
-/

namespace Examples.DesignatedContinuationSPEBoundary

open GameTree

/-- Two strategic players. -/
abbrev Player := Fin 2

def quitPayoff : Player → ℤ
  | 0 => 0
  | 1 => 0

def punishPayoff : Player → ℤ
  | 0 => -1
  | 1 => 0

def rewardPayoff : Player → ℤ
  | 0 => 1
  | 1 => 1

/-- The off-path player-`1` continuation. -/
def continuation : GameTree Player ℤ :=
  .Node 1 (.Leaf punishPayoff) [.Leaf rewardPayoff]

/-- Player `0` may quit immediately or enter `continuation`. -/
def root : GameTree Player ℤ :=
  .Node 0 (.Leaf quitPayoff) [continuation]

/-- The incredible-threat plan always chooses the head child. -/
def threat : Strategy Player ℤ :=
  fun _ head _ => ⟨head, List.mem_cons_self⟩

/-- A deviation which chooses the first tail child at player-`1` nodes and
otherwise chooses the head child. -/
def rewardDeviation : Strategy Player ℤ :=
  fun mover head tail =>
    if _hmover : mover = (1 : Player) then
      match tail with
      | [] => ⟨head, List.mem_cons_self⟩
      | child :: _rest =>
          ⟨child,
            List.mem_cons_of_mem head
              (List.mem_cons_self)⟩
    else
      ⟨head, List.mem_cons_self⟩

theorem rewardDeviation_variant :
    IVariant (1 : Player) threat rewardDeviation := by
  intro mover head tail hmover
  simp [threat, rewardDeviation, hmover]

/-- The threat profile is Nash at the whole-game root. -/
theorem threat_isNashAt_root :
    IsNashAt threat root := by
  intro i deviation hvariant
  fin_cases i
  · change
      outcome deviation
          (.Node (0 : Player) (.Leaf quitPayoff)
            [continuation]) 0 ≤
        outcome threat
          (.Node (0 : Player) (.Leaf quitPayoff)
            [continuation]) 0
    rw [outcome_Node, outcome_Node]
    let choice :=
      deviation (0 : Player) (.Leaf quitPayoff) [continuation]
    have hchoice :
        choice.1 = .Leaf quitPayoff ∨
          choice.1 = continuation := by
      simpa [choice] using choice.2
    rcases hchoice with hquit | hcontinue
    · simp [threat, choice, hquit]
    · have hplayerOne :
          deviation (1 : Player)
              (.Leaf punishPayoff) [.Leaf rewardPayoff] =
            threat (1 : Player)
              (.Leaf punishPayoff) [.Leaf rewardPayoff] :=
        (hvariant 1 (.Leaf punishPayoff) [.Leaf rewardPayoff]
          (by decide)).symm
      change
        outcome deviation choice.1 0 ≤
          outcome threat (.Leaf quitPayoff) 0
      rw [hcontinue]
      change
        outcome deviation
            (.Node (1 : Player) (.Leaf punishPayoff)
              [.Leaf rewardPayoff]) 0 ≤
          outcome threat (.Leaf quitPayoff) 0
      rw [outcome_Node, hplayerOne]
      simp [threat, punishPayoff, quitPayoff]
  · have hrootChoice :
        deviation (0 : Player)
            (.Leaf quitPayoff) [continuation] =
          threat (0 : Player)
            (.Leaf quitPayoff) [continuation] :=
      (hvariant 0 (.Leaf quitPayoff) [continuation]
        (by decide)).symm
    simp [root, outcome_Node, hrootChoice, threat, quitPayoff]

/-- The same profile is not Nash in the off-path continuation: player `1`
strictly benefits by replacing the threat with `rewardDeviation`. -/
theorem threat_not_isNashAt_continuation :
    ¬ IsNashAt threat continuation := by
  intro hnash
  have hbound :=
    hnash (1 : Player) rewardDeviation rewardDeviation_variant
  norm_num [continuation, outcome_Node, threat, rewardDeviation,
    punishPayoff, rewardPayoff] at hbound

/-- The empty complete history. -/
def initial :
    (toExtensiveGame root).toArena.HistoryFrom root :=
  Arena.HistoryFrom.nil (toExtensiveGame root).toArena root

/-- The concrete action entering the off-path continuation. -/
def enter :
    (toExtensiveGame root).Action root :=
  ⟨continuation,
    List.mem_cons_of_mem (GameTree.Leaf quitPayoff)
      List.mem_cons_self⟩

/-- The off-path continuation as a complete history occurrence. -/
def offPath :
    (toExtensiveGame root).toArena.HistoryFrom root :=
  ⟨continuation, by
    simpa [enter, root, toExtensiveGame, treeArena, arenaNext] using
      (Arena.History.nil.snoc enter)⟩

/-- A finite `GameTree` history ending back at the original root is
heterogeneously equal to the empty history: every selected child has strictly
smaller structural size. -/
theorem rootHistory_heq_nil :
    ∀ {finish : GameTree Player ℤ}
      (history : (toExtensiveGame root).toArena.History root finish),
      finish = root →
        HEq history
          (Arena.History.nil :
            (toExtensiveGame root).toArena.History root root)
  | _, .nil, _ => HEq.rfl
  | _, @Arena.History.snoc _ _ current history action, hfinish => by
      have hcurrent : Subtree current root :=
        arenaHistory_subtree history
      have hle : current.size ≤ root.size :=
        hcurrent.size_le
      cases current with
      | Leaf payoff =>
          exact nomatch action
      | Node mover head tail =>
          have hlt :
              (arenaNext (.Node mover head tail) action).size <
                (GameTree.Node mover head tail).size := by
            simpa [arenaNext] using
              (size_mem_children_lt mover head tail
                (c := action.1) (by
                  simpa [GameTree.children] using action.2))
          have :
              root.size <
                (GameTree.Node mover head tail).size := by
            simpa [toExtensiveGame, treeArena] using
              hfinish ▸ hlt
          omega

/-- A finite `GameTree` history cannot leave the root and later return to the
same root tree value. -/
theorem rootHistory_eq_nil
    (history : (toExtensiveGame root).toArena.History root root) :
    history = Arena.History.nil :=
  eq_of_heq (rootHistory_heq_nil history rfl)

/-- A complete history whose endpoint is the original finite-tree root is the
empty history occurrence. -/
theorem history_eq_initial_of_endpoint_eq
    (history :
      (toExtensiveGame root).toArena.HistoryFrom root)
    (hendpoint : history.1 = root) :
    history = initial := by
  rcases history with ⟨state, path⟩
  simp only at hendpoint
  subst state
  rw [rootHistory_eq_nil path]
  rfl

/-- An endpoint-observed presentation which designates only the whole-game
root as a continuation root. -/
def rootOnlyObserved : ExtensiveGame.ObservedGame Player ℤ :=
  toObservedGame root

/-- Initial-only analysis roots, external to the observed-game identity. -/
def rootOnlyRoots : rootOnlyObserved.RootPresentation :=
  ExtensiveGame.ObservedGame.ContinuationRootPresentation.initialOnly
    rootOnlyObserved.base

/-- The contrasting external presentation that exposes every complete
history without changing the observed-game carrier. -/
def allHistoryRoots : rootOnlyObserved.RootPresentation :=
  ExtensiveGame.ObservedGame.ContinuationRootPresentation.allHistories
    rootOnlyObserved.base

/-- The off-path continuation is absent from the initial-only domain. -/
theorem offPath_not_rootOnlyRoot :
    ¬ rootOnlyRoots.IsRoot offPath := by
  intro hroot
  have heq :
      offPath =
        Arena.HistoryFrom.nil
          rootOnlyObserved.base.toArena
          rootOnlyObserved.base.init := by
    simpa [rootOnlyRoots] using hroot
  have hendpoint :=
    congrArg (fun history => history.1) heq
  change continuation = root at hendpoint
  simp [continuation, root] at hendpoint

/-- The same off-path continuation belongs to the all-history domain. -/
theorem offPath_allHistoryRoot :
    allHistoryRoots.IsRoot offPath :=
  trivial

/-- `initialOnly` and `allHistories` have observably different continuation
domains on the same observed game. -/
theorem initialOnly_and_allHistories_differ :
    ∃ history,
      ¬ rootOnlyRoots.IsRoot history ∧
        allHistoryRoots.IsRoot history :=
  ⟨offPath, offPath_not_rootOnlyRoot, offPath_allHistoryRoot⟩

instance :
    (state : rootOnlyObserved.base.State) →
      Decidable (rootOnlyObserved.base.isTerminal state) :=
  toExtensiveGame_terminalDecidable root

theorem rootOnly_noChance :
    rootOnlyObserved.base.NoChance := by
  simpa [rootOnlyObserved] using toExtensiveGame_noChance root

theorem rootOnly_pureTerminating :
    rootOnlyObserved.PureTerminatingOnRoots
      rootOnly_noChance rootOnlyRoots := by
  intro current hroot profile
  have hcurrent : current = initial := by
    simpa [rootOnlyObserved] using hroot
  subst current
  simpa [rootOnlyObserved, rootOnly_noChance] using
    (toObservedGame_pureTerminatingOnAllContinuations
      root initial trivial profile)

/-- The initial-only presentation still admits a nonempty lawful subgame
system. It is deliberately conservative: its only root is the whole game. -/
def rootOnlySubgameSystem : rootOnlyObserved.SubgameSystem where
  IsRoot := fun current => current = initial
  init_isRoot := rfl
  lawful := by
    intro subroot hroot
    subst subroot
    simpa [rootOnlyObserved, initial] using
      rootOnlyObserved.init_isLawfulSubgameRoot

/-- The strategic threat profile translated to the root-only presentation. -/
def threatProfile : rootOnlyObserved.PureProfile :=
  playerProfileToObservedProfile root (fun _ => threat)

/-- The same endpoint-indexed threat profile in the ordinary all-history
compiler. -/
def endpointThreatProfile : (toObservedGame root).PureProfile :=
  playerProfileToObservedProfile root (fun _ => threat)

/-- The endpoint threat lifted into the occurrence-sensitive strategy
space. -/
def occurrenceThreatProfile :
    (toOccurrenceObservedGame root).PureProfile :=
  liftEndpointPureProfile root endpointThreatProfile

/-- The incredible-threat profile passes the deliberately weak
designated-continuation predicate because only the initial root is checked. -/
theorem threat_isNashOnInitialRoot :
    rootOnlyObserved.IsPureNashOnRoots
      rootOnly_noChance rootOnlyRoots rootOnly_pureTerminating
      (fun payoff => payoff) threatProfile := by
  intro current hroot
  have hcurrent : current = initial := by
    simpa [rootOnlyObserved] using hroot
  subst current
  have hcompiled :=
    (terminalContinuationGameForm_isNash_iff_isNashAt
      root (fun _ => threat) initial).mpr
        threat_isNashAt_root
  simpa [rootOnlyObserved, rootOnly_noChance,
    rootOnly_pureTerminating, threatProfile] using hcompiled

/-- Relative to the explicit conservative initial-only lawful system, the
threat satisfies subgame perfection *on that system* exactly because its sole
tested subgame is the whole game. The `On` suffix keeps this weaker coverage
visible and makes no complete standard-SPE claim. -/
theorem threat_isPureSubgamePerfectOn_rootOnly :
    rootOnlyObserved.IsPureSubgamePerfectOn
      rootOnly_noChance rootOnlySubgameSystem
      (fun current hroot =>
        rootOnly_pureTerminating current
          (by simpa [rootOnlyRoots, rootOnlySubgameSystem] using hroot))
      (fun payoff => payoff) threatProfile := by
  intro current hroot
  exact
    threat_isNashOnInitialRoot current
      (by simpa [rootOnlyRoots, rootOnlySubgameSystem] using hroot)

/-- The off-path continuation fails the corresponding local Nash test in the
ordinary all-history endpoint compiler. -/
theorem threat_fails_offPath_continuation :
    ¬ ((toObservedGame root).terminalContinuationGameForm
        (toExtensiveGame_noChance root) offPath
        ((toObservedGame_pureTerminatingOnAllContinuations root)
          offPath trivial)).IsNash
      (fun payoff : Player → ℤ => payoff)
      (playerProfileToObservedProfile root
        (fun _ => threat)) := by
  simpa [offPath] using
    (not_congr
      (terminalContinuationGameForm_isNash_iff_isNashAt
        root (fun _ => threat) offPath)).mpr
        threat_not_isNashAt_continuation

/-- The lifted threat fails standard all-history SPE in the canonical
occurrence-sensitive compiler.

If it were standard SPE, its Nash property at every lawful occurrence root
would reflect along the endpoint-information quotient.  In particular the
off-path endpoint continuation would be Nash, contradicting the explicit
profitable player-`1` deviation above. -/
theorem occurrenceThreat_not_isPureStandardSubgamePerfect :
    ¬ (toOccurrenceObservedGame root).IsPureStandardSubgamePerfect
      (toExtensiveGame_noChance root)
      (occurrenceCompleteSubgameSystem root)
      (toOccurrenceObservedGame_pureTerminatingOn root)
      (fun payoff : Player → ℤ => payoff)
      occurrenceThreatProfile := by
  intro hspe
  have hOccurrenceAllContinuations :
      (toOccurrenceObservedGame root).IsPureNashOnRoots
          (toExtensiveGame_noChance root)
          (occurrenceAllContinuationRoots root)
          (toOccurrenceObservedGame_pureTerminatingOnAllContinuations root)
          (fun payoff : Player → ℤ => payoff)
          occurrenceThreatProfile := by
    intro current _hroot
    exact hspe current trivial
  have hEndpointAllContinuations :
      (toObservedGame root).IsPureNashOnRoots
        (toExtensiveGame_noChance root)
        (endpointAllContinuationRoots root)
        (toObservedGame_pureTerminatingOnAllContinuations root)
        (fun payoff : Player → ℤ => payoff)
        endpointThreatProfile :=
    endpoint_isPureNashOnAllContinuations_of_occurrence_lift
      root (fun payoff : Player → ℤ => payoff)
      endpointThreatProfile hOccurrenceAllContinuations
  exact
    threat_fails_offPath_continuation
      (hEndpointAllContinuations offPath trivial)

/-- The occurrence presentation with the same dynamics and information but
only the initial designated root. This isolates root-coverage metadata from
the endpoint/occurrence strategy distinction. -/
def rootOnlyOccurrenceObserved : ExtensiveGame.ObservedGame Player ℤ :=
  toOccurrenceObservedGame root

/-- Initial-only analysis roots for the occurrence presentation. -/
def rootOnlyOccurrenceRoots :
    rootOnlyOccurrenceObserved.RootPresentation :=
  ExtensiveGame.ObservedGame.ContinuationRootPresentation.initialOnly
    rootOnlyOccurrenceObserved.base

/-- The off-path history is structurally lawful independently of whether the
presentation chose to designate it. -/
theorem rootOnlyOccurrence_offPath_isLawful :
    rootOnlyOccurrenceObserved.IsLawfulSubgameRoot offPath := by
  constructor
  · intro _hproper i hmover other hother hsame
    exact (congrArg Subtype.val hsame).symm
  · intro current hcurrent i hmover other hother hsame
    have hotherCurrent : other = current :=
      (congrArg Subtype.val hsame).symm
    simpa [hotherCurrent] using hcurrent

/-- A complete standard-subgame system exists independently of designated
continuation metadata. -/
theorem rootOnlyOccurrence_completeSubgameSystem_exists :
    Nonempty rootOnlyOccurrenceObserved.CompleteSubgameSystem :=
  ⟨ExtensiveGame.ObservedGame.CompleteSubgameSystem.canonical
    rootOnlyOccurrenceObserved⟩

/-- The canonical complete system includes the structurally lawful off-path
root even though the presentation does not designate it. -/
theorem rootOnlyOccurrence_canonical_admits_offPath :
    (ExtensiveGame.ObservedGame.CompleteSubgameSystem.canonical
      rootOnlyOccurrenceObserved).toSubgameSystem.IsRoot offPath :=
  rootOnlyOccurrence_offPath_isLawful

/-- Designated-root metadata remains genuinely weaker: the canonical complete
system for the initial-only presentation is not presentation-visible. -/
theorem rootOnlyOccurrence_canonical_not_presentationVisible :
    ¬ (ExtensiveGame.ObservedGame.CompleteSubgameSystem.canonical
        rootOnlyOccurrenceObserved
      ).toSubgameSystem.IsVisibleIn rootOnlyOccurrenceRoots := by
  intro hvisible
  have hdesignated :=
    hvisible offPath
      rootOnlyOccurrence_canonical_admits_offPath
  have heq : offPath = initial := by
    simpa [rootOnlyOccurrenceRoots, rootOnlyOccurrenceObserved] using
      hdesignated
  have hlength :
      offPath.2.length = initial.2.length :=
    congrArg (fun history => history.2.length) heq
  change 1 = 0 at hlength
  omega

end Examples.DesignatedContinuationSPEBoundary
