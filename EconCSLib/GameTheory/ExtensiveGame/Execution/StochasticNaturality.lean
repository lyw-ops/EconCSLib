/-
Copyright (c) 2026 EconCSLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import EconCSLib.GameTheory.ExtensiveGame.Execution.StochasticExecution
import EconCSLib.GameTheory.ExtensiveGame.Relations.Discrete.Morphism

/-!
# Naturality of bounded stochastic history execution

This neutral execution module proves exact PMF naturality under a strict
isomorphism of complete-history unfoldings.  The theorem mentions neither
payoffs nor observed-game presentations.
-/

namespace ExtensiveGame.Arena.Iso

variable {A B : Arena} {sourceStart : A.State}
  {targetStart : B.State}

/-- Exact naturality of bounded stochastic execution under a strict
isomorphism of complete-history unfoldings. -/
theorem map_stochasticHistoryPMFFrom
    [(state : A.State) → Decidable (A.IsTerminal state)]
    [(state : B.State) → Decidable (B.IsTerminal state)]
    (e :
      (A.unfoldFrom sourceStart).Iso
        (B.unfoldFrom targetStart))
    (sourcePolicy : A.StochasticHistoryPolicy sourceStart)
    (targetPolicy : B.StochasticHistoryPolicy targetStart)
    (hpolicy :
      ∀ (history : A.HistoryFrom sourceStart)
        (hsource : ¬ A.IsTerminal history.1)
        (htarget :
          ¬ B.IsTerminal (e.stateEquiv history).1),
        (sourcePolicy history hsource).map
            (e.actionEquiv history) =
          targetPolicy (e.stateEquiv history) htarget)
    (current : A.HistoryFrom sourceStart) :
    ∀ fuel,
      (A.stochasticHistoryPMFFrom
          sourcePolicy current fuel).map e.stateEquiv =
        B.stochasticHistoryPMFFrom
          targetPolicy (e.stateEquiv current) fuel := by
  intro fuel
  induction fuel generalizing current with
  | zero =>
      exact PMF.pure_map e.stateEquiv current
  | succ fuel ih =>
      by_cases hsource : A.IsTerminal current.1
      · have htarget :
            B.IsTerminal (e.stateEquiv current).1 :=
          (e.isTerminal_iff current).mp hsource
        rw [A.stochasticHistoryPMFFrom_succ_of_terminal
          sourcePolicy current fuel hsource]
        rw [B.stochasticHistoryPMFFrom_succ_of_terminal
          targetPolicy (e.stateEquiv current)
          fuel htarget]
        exact PMF.pure_map e.stateEquiv current
      · have htarget :
            ¬ B.IsTerminal (e.stateEquiv current).1 :=
          not_congr (e.isTerminal_iff current) |>.mp hsource
        rw [A.stochasticHistoryPMFFrom_succ_of_not_terminal
          sourcePolicy current fuel hsource]
        rw [B.stochasticHistoryPMFFrom_succ_of_not_terminal
          targetPolicy (e.stateEquiv current)
          fuel htarget]
        let sourceLaw := sourcePolicy current hsource
        let targetContinuation :=
          fun action =>
            B.stochasticHistoryPMFFrom targetPolicy
              ⟨B.next (e.stateEquiv current).1 action,
                (e.stateEquiv current).2.snoc action⟩
              fuel
        calc
          (sourceLaw.bind
              (fun action =>
                A.stochasticHistoryPMFFrom sourcePolicy
                  ⟨A.next current.1 action,
                    current.2.snoc action⟩
                  fuel)).map e.stateEquiv =
            sourceLaw.bind
              (fun action =>
                (A.stochasticHistoryPMFFrom sourcePolicy
                    ⟨A.next current.1 action,
                      current.2.snoc action⟩
                    fuel).map e.stateEquiv) :=
              PMF.map_bind sourceLaw
                (fun action =>
                  A.stochasticHistoryPMFFrom sourcePolicy
                    ⟨A.next current.1 action,
                      current.2.snoc action⟩ fuel)
                e.stateEquiv
          _ = sourceLaw.bind
              (fun action =>
                B.stochasticHistoryPMFFrom targetPolicy
                  (e.stateEquiv
                    ⟨A.next current.1 action,
                      current.2.snoc action⟩)
                  fuel) := by
            apply congrArg (fun continuation =>
              sourceLaw.bind continuation)
            funext action
            exact ih
              ⟨A.next current.1 action,
                current.2.snoc action⟩
          _ = sourceLaw.bind
              (targetContinuation ∘
                e.actionEquiv current) := by
            apply congrArg (fun continuation =>
              sourceLaw.bind continuation)
            funext action
            unfold targetContinuation
            apply congrArg
              (fun next =>
                B.stochasticHistoryPMFFrom
                  targetPolicy next fuel)
            exact e.map_next current action
          _ = (sourceLaw.map
                (e.actionEquiv current)).bind
              targetContinuation :=
            (PMF.bind_map sourceLaw
              (e.actionEquiv current)
              targetContinuation).symm
          _ = (targetPolicy
                (e.stateEquiv current) htarget).bind
              targetContinuation := by
            rw [hpolicy current hsource htarget]
            rfl

end ExtensiveGame.Arena.Iso
