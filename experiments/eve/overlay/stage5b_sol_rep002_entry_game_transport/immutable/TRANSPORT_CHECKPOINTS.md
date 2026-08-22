# Frozen transport-route checkpoints

The final concrete theorem signatures in `solver/README.md` are immutable.
Complete these checkpoints in order without weakening the deterministic
evaluator:

1. Freeze the exact final concrete theorem signatures.
2. Define the action encoders and the profile encoder.
3. Prove payoff preservation.
4. Bridge the exercise's strict assumptions to the general theorem's
   assumptions.
5. Prove Nash and subgame-perfect-equilibrium preservation.
6. Construct the complete `RefinementCertificate`.
7. Explicitly consume the certificate's preservation projections.
8. Invoke the fixed general `AbstractTwoStage` theorems.
9. Prove encoded-profile equality reflection, or reflect equality by complete
   case analysis on the concrete actions.
10. Transport both conclusions back to the concrete profile type and the exact
    declarations required by `solver/README.md`.
