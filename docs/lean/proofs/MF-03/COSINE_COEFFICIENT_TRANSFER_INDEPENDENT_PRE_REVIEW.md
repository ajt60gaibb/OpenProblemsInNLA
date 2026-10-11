# MF-03 cosine coefficient transfer: independent pre-review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen exact contract for implementation. It identifies the infinite product's elementary coefficients with the factorial series but leaves the Padé Schur bound and full Target open.

| Reviewed input | SHA-256 |
| --- | --- |
| `COSINE_COEFFICIENT_TRANSFER_PRE_REVIEW.md` | `8ba96613cfc09c64cc8b4d49c5b9d79986a21c63374b96d8c78f66db7d24528f` |
| Frozen `NLA.Statements.MF03` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| Audited all-complex product source | `59b6a9cf45df57ae13933abf6aecbbcce47f8c63269f8219b9dcd7cdbd016dbc` |

The factors are indexed `k≥0` with `a_k=cosineFactor(k+1)>0`, so the first is `a₀=4/π²`. Absolute summability of `a_k` gives absolute summability of complex `a_kz` for every `z`. The pinned `summable_finsetProd_of_summable_norm` and `tprod_one_add` then expand the actual infinite product as an unconditional sum over finite subsets. The equivalence between a finite subset and its cardinality fiber permits a sigma regrouping because of that absolute summability. On each cardinality-`j` fiber, finite product algebra gives exactly `z^j∏a_k`; the real nonnegative fiber sum is summable and its complex cast is legitimate. The `j=0` fiber contains only the empty subset and has coefficient one.

The previously audited all-complex identity equates the regrouped sum to `waveSeries z` for every complex `z`. This value equality alone is insufficient for coefficient equality. The contract correctly requires a common positive convergence radius and pinned formal multilinear series uniqueness. Summability of the nonnegative elementary coefficients at radius one follows from the same absolute grouping; factorial coefficients are summable at radius one. The pinned `ofScalars_norm`, `le_radius_of_summable_norm`, `hasFPowerSeriesOnBall`, `ofScalars_sum_eq`, and `HasFPowerSeriesAt.eq_formalMultilinearSeries` support this route. The coefficient result is exactly `e_j=1/(2j)!` for all `j`, including zero.

The stated first checks `e₀=1`, `e₁=1/2`, and `e₂=1/24` match the factorial formula; the Schur tail starts at factor index `k=m` (one-based manuscript `ν>m`) and equals the existing `cosineTail m`. The proposed exports assert no Schur determinant, tableau bound, denominator existence, or full Padé Target. Implementation must preserve the finite-subset type and prove absolute regrouping and analytic uniqueness without substituting a merely formal coefficient identity. Keep the new source unimported until a separate source/signature/LeanCert audit.
