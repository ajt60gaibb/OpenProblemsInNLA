# SP-14 actual base-jet real solve: independent Lean review

**Reviewer:** `/root` (AI agent), 10 October 2026. **Verdict:** APPROVE frozen `BaseJetRealSolve.lean` for the exact unperturbed finite real jet system. It is not a correction-vector theorem for the source's later perturbed backgrounds and does not prove `NLA.Statements.SP14.Target`.

I read the full source and compared its elaborated public statements with the independently approved real-solve contract. The source zero-pads a real `Fin h` vector into the actual complete restored packet. It extracts coefficients of the already audited **actual** `oddJetPolynomial` formula, proves the base `X^m` term vanishes for `k<h≤q` under `2q≤m+1`, and reindexes the finite packet sum exactly. The first `h` complex coefficients are the complex casts of `(baseJetMatrix h).mulVec u`; their imaginary parts are zero. Thus the defined real jet map is exactly this real matrix map for every input, including the empty `m=q=h=0` endpoint.

The source applies the previously audited triangular inverse to produce an explicit real padded vector for **every** desired first-`h` jet, proves the corresponding actual coefficient values and zero-jet predicate, and proves uniqueness only in the selected first-`h` real coordinates. It does not incorrectly assert uniqueness among all `q` variables when `q>h`. Its finite difference theorem identifies the same actual map with `J⁰`; the `HasFDerivAt` and `fderiv` theorems identify its derivative at every input with the matrix-induced continuous linear map, and the nonzero determinant proves that derivative bijective. This is the precise finite base-model regularity claim, not an assumed Jacobian.

I separately imported the frozen module under pinned Lean 4.33.1, checked all public signatures, ran LeanCert `#assert_trust kernel` for the coefficient, solve, uniqueness, and derivative theorems, and printed their transitive axioms. The audit exited 0 and reports only `propext`, `Classical.choice`, and `Quot.sound`. A source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/SP14/BaseJetRealSolve.lean`** | **`928d76ed84d4310e5feafa53c13bbf78490208ae5efafaca169f0556d6100dbe`** |
| Approved `BASE_JET_REAL_SOLVE_PRE_REVIEW.md` | `dce71f8dba14a042665cf27a07be3a34447db8aa3d6e80f90d85f4223fbd0a4f` |
| Independent mathematical pre-review | `3beb63a09cbdfd3856a45bbecb9d51343e7d8e6833be9066cac098efedc8cf77` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Imported `/private/tmp/sp14-basejetrealsolve-independent-audit.lean` | `cc3850c38eb51b488f2d66ab0ef86b18aad6f98aa3a8fff9568b8df15b63e1e6` |

Changed source or contract bytes reopen this review. The later analytic all-background stage, norm budgets, infinite symbol, two-sided nonextension, and final empirical gap remain unproved.
