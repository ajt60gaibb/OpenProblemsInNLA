# TR-14 local top-coefficient algebra: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen first local-algebra source for aggregate import. It proves exact truncated coefficients and Frobenius-element representation, not local nondegeneracy, nth roots, CRT, width, or the frozen Target.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/TR14/LocalTopCoefficient.lean` | `0803a7a5c625b364527b4cbbcbba825d6dd410c81ef648018e18ee4f5cfc3275` |
| Exact local top-coefficient contract | `c5797947009882f77bacc12d3a3f641178a38a6aa134ffc842aba9cb9ecab37b` |
| Independent mathematical pre-review | `a1956c229aaa16e4d157e8eb25cd33db09dcd495eae45babb7b96bbe9a6072cf` |
| Canonical `solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| Frozen `NLA.Statements.TR14` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Separate imported audit `/private/tmp/tr14-localtopcoeff-independent-audit.lean` | `3a4761354eba0c7d9179fd8bea9bfc49313e6b7f557066a4acf1538d6aae69eb` |

The source uses the actual quotient `AdjoinRoot (X^ℓ)` and its monic power basis indexed by `Fin ℓ`. It proves `z^ℓ=0`, exact low-degree coefficients of quotient images, full truncated antidiagonal convolution for every coefficient `j<ℓ`, and that the `Fin ℓ` coefficients reconstruct and determine every local class. Thus no polynomial representative is silently evaluated at a complex point.

The reversed element has coefficient `u_j=Λ(z^(ℓ−1−j))` exactly. Multiplication by `z^j` shifts the top coefficient to `u_(ℓ−1−j)`, so the source proves `Λ(a)=top(u a)` by equality of linear maps on the power basis, for **every** local class `a`. The same shifted-coordinate argument proves uniqueness of `u`. These statements include `ℓ=1` and require no Frobenius hypothesis yet. The source does not infer `u₀≠0` or an nth root before the separate nondegeneracy step.

The pinned Lean 4.33.1 direct module build passed 3,037 jobs. My separate imported LeanCert audit exited zero, checked definitions and public signatures, reran `#assert_trust kernel`, and printed only `[propext, Classical.choice, Quot.sound]` for convolution, representation, and uniqueness. A frozen-source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

Local Frobenius nondegeneracy, `u₀≠0`, finite mth root, global CRT transfer, symmetric width upper constructions, arbitrary ordinary lower bound, and full TR-14 Target remain open.
