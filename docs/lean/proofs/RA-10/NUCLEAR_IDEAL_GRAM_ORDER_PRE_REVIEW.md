# RA-10 sharp Gram order for the left nuclear ideal bound

**Status:** source-locked mathematical, numerical, and exact-signature precontract for independent review. No Lean implementation or proof is claimed. This is a dependency for the approved coefficient-one nuclear ideal inequality, not that inequality or the final `RA-10` Target.

## Source locks and norm semantics

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `docs/lean/proofs/RA-10/NUCLEAR_IDEAL_EQ14_PRE_REVIEW.md` | `77da0117b61b482c844382ab4893ad0553b48fce67a66d807a7f42809cdbd3ef` |
| `lean-statements/NLA/Proofs/RA10/NuclearIdealOperatorBridge.lean` | `27a30c33bb8b758013f99e1775c01d0515d90b3a4fe62ceb60d28fc9d8cf5ced` |
| `lean-statements/NLA/Proofs/RA10/CustomPSDMathlibBridge.lean` | `ca0e97485f3538275f12006d3619687d4c49bf0c1e7a8e2f698dadf87b64e0b7` |
| `lean-statements/NLA/Proofs/RA10/OrderedPSDLoewnerEigenvalue.lean` | `66a356e2ebc291b2d0c7b272ad770041414e1b2a66330acf46f23f1bdbe0fc73` |

Under **`open scoped Matrix.Norms.L2Operator`**, `‖X‖` is the Euclidean induced operator norm. The audited `matrix_l2_opNorm_eq_operator_norm` identifies it with `‖Matrix.toEuclideanCLM X‖`. It is distinct from the frozen nuclear norm `Σ_{i:Fin n}(Matrix.toEuclideanLin X).singularValues i.val`. This contract uses the former only for a sharp Gram comparison needed to bound the latter later.

## Exact mathematical and numerical statement

For every `n : ℕ` and arbitrary real square matrices `X,Y`, let `G=YᵀY` and `H=(XY)ᵀ(XY)`. Prove the **frozen custom PSD predicate** on their exact difference:

```text
PositiveSemidefinite ((‖X‖₂→₂²) • (YᵀY) − (XY)ᵀ(XY)).
```

The scalar is exactly `‖X‖²` with coefficient one; there is no dimension/rank factor. The order is `(‖X‖²)G−H`, so a later ordered-eigenvalue comparison gives the useful direction `eigenvalue(H,i)≤‖X‖² eigenvalue(G,i)`. The matrices need not be symmetric, positive, invertible, commuting, or full rank. It includes `X=0`, `Y=0`, tied/zero singular values, and `n=0` with the empty vector space.

## Proof obligation

First prove the matrix difference is symmetric, using transpose of each real Gram matrix and the real scalar action. For each `x:Fin n→ℝ`, its frozen double quadratic sum is exactly

```text
‖X‖² · ‖Yx‖₂² − ‖X(Yx)‖₂².
```

Here `Yx` and `X(Yx)` are Euclidean vectors represented by the **same** `Matrix.toEuclideanCLM` operators that define the scoped norm; matrix multiplication has the exact `XY` order. The pinned continuous-linear-map norm inequality `‖Xv‖₂≤‖X‖₂→₂‖v‖₂` for `v=Yx`, with nonnegative norms, proves the quadratic expression nonnegative after squaring. The quadratic identity and norm conversion must be kernel-proved; one may instead use pinned `Matrix.PosSemidef` APIs and then the audited exact iff to return to `NLA.Statements.RA10.PositiveSemidefinite`. No assumption of the desired PSD statement is permitted.

## Proposed exact Lean declaration

Implement in a separate `NLA.Proofs.RA10.NuclearIdealGramOrder` module after independent approval. Its matrix norm scope is mandatory:

```lean
open scoped Matrix.Norms.L2Operator

namespace NLA.Proofs.RA10

theorem nuclearIdeal_left_gram_order {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.PositiveSemidefinite
      ((‖X‖ ^ 2) • (Y.transpose * Y) -
        (X * Y).transpose * (X * Y)) := by
  ...

end NLA.Proofs.RA10
```

This statement deliberately does not yet mention a chosen Gram eigendecomposition or infer the nuclear ideal inequality. Subsequent gates must construct/transfer the ordered real PSD Gram spectra, compare every same-index squared singular value, take the nonnegative square roots, and sum over all `Fin n`; no nuclear norm substitute is allowed.

## Review and verification gate

Independent review must check the scoped Euclidean operator norm, exact Gram order and transpose, squared scalar and coefficient one, custom PSD predicate including symmetry, product orientation, zero matrices and `Fin 0`. Only after approval may Lean implementation begin. Direct pinned LeanCert kernel checks, frozen source SHA, and separate imported exact-signature/source/axiom audit are required before aggregate import. No `sorry`, `admit`, custom axiom, `native_decide`, unsafe declaration, or per-order computation.
