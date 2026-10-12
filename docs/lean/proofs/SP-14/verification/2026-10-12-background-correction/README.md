# SP-14 completed-inverse correction: independent LeanCert receipt

The imported exact-signature audit is [`independent-audit.lean`](independent-audit.lean), SHA-256 `ef16d6445fc511e1546687b80700a40c0175074e7a7002f46b34e68aade9bc88`. It checks both full public theorem statements and invokes `#assert_trust kernel` and `#print axioms` for each.

From `lean-statements/`, with the pinned Lean 4.33.1 toolchain and the project's Lake dependencies available:

```sh
lake env lean ../docs/lean/proofs/SP-14/verification/2026-10-12-background-correction/independent-audit.lean
lake build NLA.Proofs
```

The same-byte audit and aggregate build passed on the SP-14 split branch at `625be6ac`; the aggregate build completed 3,141 jobs. The committed audit copy was also rechecked in this branch. Both printed axiom lists were exactly `propext`, `Classical.choice`, and `Quot.sound`. The audited source [`EndpointBackgroundCorrectionL2.lean`](../../../../../../lean-statements/NLA/Proofs/SP14/EndpointBackgroundCorrectionL2.lean) has SHA-256 `d2f59e145006db6eca49a836ef57e077803bafd1b49b2af57fadb495cbe08785`. This receipt covers the finite correction's coefficient-sum and `L²` energy bounds; the frozen SP-14 Target remains open.
