# RA-10 Equation (6) independent LeanCert receipt

The imported exact-signature audit is [`independent-audit.lean`](independent-audit.lean), SHA-256 `89ac45653c4072d0bddd0d980788355a93836bfcee168143ec9b9932a03a2b79`. It checks the full public theorem statement for the actual selected compression and invokes `#assert_trust kernel` and `#print axioms`.

From `lean-statements/`, with the pinned Lean 4.33.1 toolchain and the project's Lake dependencies available:

```sh
lake env lean ../docs/lean/proofs/RA-10/verification/2026-10-12-eq6/independent-audit.lean
lake build NLA.Proofs
```

The same-byte independent audit and aggregate build passed on the RA-10 split branch at `5f02ff12`; the aggregate build completed 2,788 jobs. The committed audit copy was also rechecked in this branch. The theorem's printed axioms were exactly `propext`, `Classical.choice`, and `Quot.sound`. The audited source [`RidgeCompressionEq6Eigenvector.lean`](../../../../../../lean-statements/NLA/Proofs/RA10/RidgeCompressionEq6Eigenvector.lean) has SHA-256 `257b096791352fd2faab693f374d8d91a0843d5d77446a84ca79bff686bb2bd9`. This receipt covers only Equation (6), not the coefficient-two Lemma 2 or the RA-10 Target.
