# SP-14 regularized exterior factor Fourier series: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen source for aggregate import. This proves the actual pointwise factor's circle series and every Fourier coefficient under the frozen real-interval integral. It does not prove a Wiener product bound or the SP-14 Target.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP14/RegularizedBaseFactorFourier.lean` | `2afdee09ed97dbae6b64529c8a0af23c322ce57619e6b658e3355f52872b64fc` |
| Exact pre-implementation contract | `6cc17eebf8c7664f6945a0405e4755c5cfaac2d2d023562968ca79a4ccf4f119` |
| Independent mathematical pre-review | `e65b999e7c0112642a47b12c2dadffcc37086dd4e86ed4c56d83f2ade5c09b4e` |
| Separate imported audit `/private/tmp/sp14-regularizedfactorfourier-independent-audit.lean` | `f6e1671793ba333cadbeca165dc18d9b381eb5b17709ccfd3eb4b7304c056bfb` |

The definition is exactly `(1+s)g₀(s)` on `Circle`. In the absolutely convergent base series, multiplication by `s` extracts `c₀s=s` and shifts the remaining negative powers. The coefficient of `s⁻ⁿ` is exactly `dₙ=cₙ+cₙ₊₁`, including `n=0`. The proof does not divide at `s=-1`.

The Fourier proof applies the reviewed pure-mode integral identity to the actual frozen `FourierCoefficient`, whose phase is `e⁻ⁱᵏᵗ` and whose normalization is `1/(2π)`. Norm summability of the regularized coefficients permits compact-interval termwise integration. The result is `1` at `k=1`, `d_(natAbs k)` for every `k≤0`, and `0` at every remaining positive frequency. The cases are disjoint and cover all integers.

The pinned Lean 4.33.1 direct module build passed 2,763 jobs. My separate imported LeanCert audit exited zero, checked the public definition and theorem signatures, reran `#assert_trust kernel` on continuity, series, and Fourier identity, and printed only `[propext, Classical.choice, Quot.sound]` for the series and Fourier theorem. A frozen-source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

The bilateral Wiener norm estimate, endpoint inverse, nonlinear background construction, final counterexample, and full SP-14 Target remain open.
