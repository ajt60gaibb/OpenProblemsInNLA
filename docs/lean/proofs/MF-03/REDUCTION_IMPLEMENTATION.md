# MF-03 generic reduction implementation

The frozen pre-proof contract is
`docs/lean/proofs/MF-03/REDUCTION_PRE_REVIEW.md` (SHA-256
`331d29fb2c700a53dee761fe27adcda91bcb383c08481d5da4557800fd208d37`).
The independent mathematical pre-review approved it in
`docs/lean/proofs/MF-03/REDUCTION_INDEPENDENT_PRE_REVIEW.md`.

The new module `lean-statements/NLA/Proofs/MF03/Reduction.lean` exports
`NLA.Proofs.MF03.normalized_exists_reduced` with the exact contracted
signature. It divides a normalized pair by its polynomial gcd, rescales by
the gcd's value at zero, and proves that all Padé coefficient equations
through `2*m` survive cancellation. The latter proof is an induction on the
coefficient of a formal power-series product. The output includes the
cross-product identity `Pᵣ * Q = P * Qᵣ`.

Verification command, run from `lean-statements` with the pinned Lean 4.33.1
binary on `PATH`:

```bash
lake build NLA.Proofs.MF03.Reduction
```

This exited zero. `#assert_trust kernel normalized_exists_reduced` passed.
`#print axioms` reported exactly `[propext, Classical.choice, Quot.sound]`.
The module contains no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`,
`native_decide`, `implemented_by`, or `run_tac`.

SHA-256 at implementation verification:

| File | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/MF03/Reduction.lean` | `0e58cdba5a4302aa025201e73143a4c3056f33fc43c618da6bf4aa0095da89cb` |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |

This lemma turns each already constructed normalized pair into an existential
reduced pair. It supplies no normalized pair for any new order, so it does not
by itself prove the all-order `Target`. The existing finite certificates and
disk transport theorem were not changed.
