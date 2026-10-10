# TR-14 normalized quotient Frobenius pairing: independent Lean review

**Reviewer:** `/root` (AI agent), 10 October 2026. **Verdict:** APPROVE frozen `FrobeniusMinimal.lean` for the conditional normalized quotient pairing. This proves no chart transport, middle catalecticant rank, or full `NLA.Statements.TR14.Target`.

I read the complete source and compared its elaborated theorem with the independently approved `QUOTIENT_FROBENIUS_PRE_REVIEW.md`. It retains a nonzero moment vector, a monic polynomial of positive exact `natDegree r₀≤D`, the exact degree-`r₀` apolar equations, and triviality of every lower homogeneous apolar kernel. The conclusion is full nondegeneracy: for **every** `a` in `AdjoinRoot g`, vanishing of `λ(a*b)` for every `b` forces `a=0`. Frobenius nondegeneracy is proved, not supplied as a premise.

The proof expands an arbitrary radical element uniquely in the quotient power basis `1,t̄,…,t̄^{r₀−1}`. For every allowed shift, the radical equation with `b=t̄^j` and the already audited all-moment identity converts those coefficients into an exact apolar vector of degree `r₀−1`. The `hmin` premise forces this vector to vanish; the power-basis sum then forces `a=0`. This direct argument covers `r₀=1` through degree-zero apolarity and uses the final moment through `D`. It avoids the larger ideal-correspondence construction permitted by the contract. The explicit `h≠0` input is retained, although the proof does not need it separately once the lower-kernel premise is present; this does not strengthen a later global Target.

I separately imported the frozen module under pinned Lean 4.33.1, checked the exact elaborated signature, ran LeanCert `#assert_trust kernel`, and printed transitive axioms. The audit exited 0 and reports only `propext`, `Classical.choice`, and `Quot.sound`. A source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/TR14/FrobeniusMinimal.lean`** | **`dca235b899ba5729e5bdfb50986e55836989c2736b133ee6e2b4a7f428dee29e`** |
| Approved `QUOTIENT_FROBENIUS_PRE_REVIEW.md` | `3b8d8d1484755f149c61feb992255c6be617f659219eb0c1bf96b165c0134eea` |
| Independent mathematical pre-review | `7cdcdb40e1a9f5d9fe68b12b6a14a93be8af7bcc39b0d18e19b1eb80114a4216` |
| Imported `/private/tmp/tr14-frobenius-independent-audit.lean` | `5913fa44082dd995242e2595b8bccd7a5503eca61aa6198e5bbe2cc7f2ca53ce` |

Changed source or contract bytes reopen this review.
