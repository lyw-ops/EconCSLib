# Transport route solver contract

Edit only `Candidate.lean` below the solver marker. Add exactly:

- `encodeChallenger`, `encodeIncumbent`, and `encodeProfile`;
- `entryUtilities`;
- `payoff_preserved` and `hypothesis_bridge`;
- `nash_preserved` and `subgamePerfect_preserved`;
- `entryCertificate : RefinementCertificate`;
- `abstract_nash_for_entry` using `AbstractTwoStage.nash_iff_of_strict`;
- `abstract_unique_spe_for_entry` using
  `AbstractTwoStage.unique_spe_of_strict`;
- `transport_subgamePerfect_iff`;
- `transport_out_fight_separation`.

The conclusion theorems must be transported through `entryCertificate`; a
second direct enumeration of the concrete payoff table does not satisfy this
route. Do not add imports, placeholders, axioms, or trusted bypasses.
