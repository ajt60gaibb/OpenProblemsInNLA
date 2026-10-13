# MF-03 finite-range theorem implementation

The mathematical pre-proof contract in `FINITE_RANGE_PRE_REVIEW.md`
(SHA-256 `026f12f8ac3c180e482bbb05088c72c2c5d212650568b8350cb39f10db0cb814`)
received independent approval before implementation.

The new `lean-statements/NLA/Proofs/MF03/FiniteRange.lean` module exports
`NLA.Proofs.MF03.target_through_fifteen` with the exact reviewed signature.
It proves both existence of a reduced normalized pair and the closed-disk
pole-free error bound for every reduced pair at each order `1 ≤ m ≤ 15`.
For orders 2 through 15, it uses the existing normalized and disk
certificates, generic gcd reduction, and disk transport. Order 1 uses the
existing complete target clause.

From `lean-statements`, both pinned-toolchain commands exited zero:

```bash
lake build NLA.Proofs.MF03.FiniteRange
lake env lean NLA/Proofs/MF03/FiniteRange.lean
```

The module's `#assert_trust kernel target_through_fifteen` passed, and
`#print axioms` reported exactly `[propext, Classical.choice, Quot.sound]`.
The source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`,
`native_decide`, `implemented_by`, or `run_tac`.

SHA-256 of `FiniteRange.lean` at verification:
`b83eadb2aa7bb33dfaf8f553be0ae16df5cab60762a90ff11cea2e609f38278a`.
The frozen statement remained at
`35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24`.

This theorem has an explicit `m ≤ 15` hypothesis. No theorem for larger
orders, and therefore no proof of the all-order `Target`, is claimed here.
