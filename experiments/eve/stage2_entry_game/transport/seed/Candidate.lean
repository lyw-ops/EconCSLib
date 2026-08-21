import EconCSLib.GameTheory.ExtensiveGame.Interface.Compilation.Discrete
import Mathlib.Tactic

/-!
# Stage 2 Entry Game — transport route

The fixed prefix contains the concrete exercise model and an abstract reusable
two-stage theorem. Build the explicit refinement certificate and transport the
abstract conclusions back to the exercise below the solver marker.
-/

namespace EconCSLibEVEEntryGameTransport

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

namespace AbstractTwoStage

inductive FirstAction
  | enter
  | stayOut
  deriving DecidableEq, Fintype

inductive Reply
  | acquiesce
  | fight
  deriving DecidableEq, Fintype

abbrev Profile := FirstAction × Reply

structure Utilities where
  outChallenger : ℤ
  outIncumbent : ℤ
  acquiesceChallenger : ℤ
  acquiesceIncumbent : ℤ
  fightChallenger : ℤ
  fightIncumbent : ℤ

def payoff (u : Utilities) : Profile → Player → ℤ
  | (.stayOut, _), .challenger => u.outChallenger
  | (.stayOut, _), .incumbent => u.outIncumbent
  | (.enter, .acquiesce), .challenger => u.acquiesceChallenger
  | (.enter, .acquiesce), .incumbent => u.acquiesceIncumbent
  | (.enter, .fight), .challenger => u.fightChallenger
  | (.enter, .fight), .incumbent => u.fightIncumbent

def IsNash (u : Utilities) (profile : Profile) : Prop :=
  (payoff u (.enter, profile.2) .challenger ≤
      payoff u profile .challenger ∧
    payoff u (.stayOut, profile.2) .challenger ≤
      payoff u profile .challenger) ∧
  (payoff u (profile.1, .acquiesce) .incumbent ≤
      payoff u profile .incumbent ∧
    payoff u (profile.1, .fight) .incumbent ≤
      payoff u profile .incumbent)

def IsOptimalAfterEntry (u : Utilities) (reply : Reply) : Prop :=
  payoff u (.enter, .acquiesce) .incumbent ≤
      payoff u (.enter, reply) .incumbent ∧
    payoff u (.enter, .fight) .incumbent ≤
      payoff u (.enter, reply) .incumbent

def IsSubgamePerfect (u : Utilities) (profile : Profile) : Prop :=
  IsNash u profile ∧ IsOptimalAfterEntry u profile.2

structure StrictEntryConditions (u : Utilities) : Prop where
  enter_beats_out_when_acquiesce : u.outChallenger < u.acquiesceChallenger
  out_beats_enter_when_fight : u.fightChallenger < u.outChallenger
  acquiesce_beats_fight : u.fightIncumbent < u.acquiesceIncumbent

theorem nash_iff_of_strict (u : Utilities) (h : StrictEntryConditions u)
    (profile : Profile) :
    IsNash u profile ↔
      profile = (.enter, .acquiesce) ∨
      profile = (.stayOut, .fight) := by
  rcases profile with ⟨first, reply⟩
  rcases h with ⟨henter, hout, hacquiesce⟩
  cases first <;> cases reply <;>
    simp [IsNash, payoff] at * <;> omega

theorem unique_spe_of_strict (u : Utilities) (h : StrictEntryConditions u)
    (profile : Profile) :
    IsSubgamePerfect u profile ↔ profile = (.enter, .acquiesce) := by
  rcases profile with ⟨first, reply⟩
  rcases h with ⟨henter, hout, hacquiesce⟩
  cases first <;> cases reply <;>
    simp [IsSubgamePerfect, IsNash, IsOptimalAfterEntry, payoff] at * <;>
    omega

end AbstractTwoStage

structure RefinementCertificate where
  encode : PureProfile → AbstractTwoStage.Profile
  utilities : AbstractTwoStage.Utilities
  payoff_preserved : ∀ profile player,
    normalPayoff profile player = AbstractTwoStage.payoff utilities (encode profile) player
  hypothesis_bridge : AbstractTwoStage.StrictEntryConditions utilities
  nash_preserved : ∀ profile,
    IsNash profile ↔ AbstractTwoStage.IsNash utilities (encode profile)
  subgamePerfect_preserved : ∀ profile,
    IsSubgamePerfect profile ↔
      AbstractTwoStage.IsSubgamePerfect utilities (encode profile)

/-! ## Solver declarations: transport route -/

end EconCSLibEVEEntryGameTransport
