# Direct route solver contract

Edit only `Candidate.lean` below the solver marker. Add exactly these theorems:

```lean
theorem direct_nash_iff (profile : PureProfile) :
    IsNash profile ↔
      profile = (.enter, .acquiesce) ∨
      profile = (.stayOut, .fight)

theorem direct_subgamePerfect_iff (profile : PureProfile) :
    IsSubgamePerfect profile ↔ profile = (.enter, .acquiesce)

theorem direct_out_fight_separation :
    IsNash (.stayOut, .fight) ∧
      ¬ IsSubgamePerfect (.stayOut, .fight)
```

Use the concrete payoff table directly. Do not add imports, declarations with
different types, placeholders, axioms, unsafe/trusted bypasses, or an abstract
transport model.
