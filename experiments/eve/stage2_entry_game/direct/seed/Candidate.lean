import EconCSLib.GameTheory.ExtensiveGame.Interface.Compilation.Discrete
import Mathlib.Tactic

/-!
# Stage 2 Entry Game — direct route

The fixed prefix is the concrete exercise model. Add only the three required
direct-route theorems below the solver marker. Do not encode the abstract
transport template in this route.
-/

namespace EconCSLibEVEEntryGameDirect

open ExtensiveGame

inductive Player
  | challenger
  | incumbent
  deriving DecidableEq, Fintype

inductive ChallengerAction
  | enter
  | stayOut
  deriving DecidableEq, Fintype

inductive IncumbentAction
  | acquiesce
  | fight
  deriving DecidableEq, Fintype

inductive TerminalHistory
  | out
  | enterAcquiesce
  | enterFight
  deriving DecidableEq, Fintype

def payoff : TerminalHistory → Player → ℤ
  | .out, .challenger => 1
  | .out, .incumbent => 2
  | .enterAcquiesce, .challenger => 2
  | .enterAcquiesce, .incumbent => 1
  | .enterFight, _ => 0

abbrev PureProfile := ChallengerAction × IncumbentAction

def play : PureProfile → TerminalHistory
  | (.stayOut, _) => .out
  | (.enter, .acquiesce) => .enterAcquiesce
  | (.enter, .fight) => .enterFight

def normalPayoff (profile : PureProfile) (player : Player) : ℤ :=
  payoff (play profile) player

def tree : GameTree Player ℤ :=
  .Node .challenger
    (.Leaf (payoff .out))
    [.Node .incumbent
      (.Leaf (payoff .enterAcquiesce))
      [.Leaf (payoff .enterFight)]]

def IsNash (profile : PureProfile) : Prop :=
  (∀ deviation : ChallengerAction,
      normalPayoff (deviation, profile.2) .challenger ≤
        normalPayoff profile .challenger) ∧
    (∀ deviation : IncumbentAction,
      normalPayoff (profile.1, deviation) .incumbent ≤
        normalPayoff profile .incumbent)

def IsOptimalAfterEntry (action : IncumbentAction) : Prop :=
  ∀ deviation : IncumbentAction,
    normalPayoff (.enter, deviation) .incumbent ≤
      normalPayoff (.enter, action) .incumbent

def IsSubgamePerfect (profile : PureProfile) : Prop :=
  IsNash profile ∧ IsOptimalAfterEntry profile.2

/-! ## Solver declarations: direct route -/

end EconCSLibEVEEntryGameDirect
