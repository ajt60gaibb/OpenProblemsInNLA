# MF-23 independent review of the canonical Lean statement

**Reviewer:** `/root`, 9 October 2026. **Verdict:** APPROVE the statement as an exact finite matrix-polynomial formulation of the published MF-23 target. This approval precedes implementation of the factor-swap proof and does not certify `Target`.

I compared the published README, the pinned upstream `Model.lean`, and `CanonicalStatement.lean` line by line. `CanonicalUniversalBound 2` quantifies over all positive base and coefficient sizes `n,m`, every finite degree `d`, all complex square `A`, and all complex matrix coefficients `B`. Trailing zero coefficients allow every matrix polynomial. The value `blockEvaluation A B = ∑ k, B k ⊗ₖ A ^ k` has indices `Fin m × Fin n`; its `(i,r),(j,s)` entry is `∑ k, (B k) i j * (A ^ k) r s`, exactly the `(r,s)` entry of the README's block `fᵢⱼ(A)`. No extra hypothesis or restricted numerical-range shape appears.

The right side uses the upstream `rangeMaximum A B` *without alteration*. Its source is the supremum of the Euclidean operator norm of `∑ k, z^k • B k` over the full upstream `numericalRange A`; the pinned `NumericalRange.lean` proves this supremum is attained for `0 < n`. The same `Matrix.Norms.L2Operator` scope supplies both matrix norms, matching the induced Euclidean operator norms in the README. The literal real `2` is independent of all dimensions and the degree.

The upstream `tensorEvaluation` reverses the two Kronecker factors, so `complete_crouzeix : UniversalBound 2` does **not** definitionally prove this canonical statement. A Lean proof of the factor-swap permutation preserving the operator norm is still required. There is no frozen shared `NLA.Statements.MF23.Target` in this branch. I independently elaborated `CanonicalStatement.lean` with the pinned Lean 4.34.1 scratch dependencies; it passed with no errors. This checks the declaration's type, not its truth.

## SHA-256 review inputs

| Input | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-23/README.md` | `ce65d34a504156e52e9b917419b7f3a0bf605cea219a4b627197de470ffbe324` |
| `matrix-functions-and-stability/MF-23/lean/CanonicalStatement.lean` | `9ce2eff57267fcccf4b6bf39c06754d65f8d4bf19316254cfa2a7372bfc11f81` |
| pinned upstream `Model.lean` | `3be01360e343e41c9712883d81e8845122ef13b2418640fa32c5e2fd22cdba84` |
| pinned upstream `NumericalRange.lean` | `3b29e7e106eb2aafdcb4e2aa302ae0a1978c65c0dceb746344e6322a37bfb919` |

The last hash identifies the upstream maximum-attainment proof. The upstream theorem itself and the new bridge require separate kernel and Comparator audits.
