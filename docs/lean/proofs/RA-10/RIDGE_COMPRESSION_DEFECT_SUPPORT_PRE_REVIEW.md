# RA-10 Lemma 2 support gate: selected compression deficit trace

**Status:** source-only mathematical/indexing precontract for an exact staged helper toward `RIDGE_COMPRESSION_POSITIVE_PART_PRE_REVIEW.md`. No Lean implementation is claimed. An additional public signature needs independent review before implementation.

## Frozen sources and audited dependencies

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `lean-statements/NLA/Proofs/RA10/HermitianPositivePart.lean` | `db272c38e076cd0e41a278d9a488f5aba5cab71f1104f146236f591a8ef3f6e8` |
| `lean-statements/NLA/Proofs/RA10/SelectedCompressionPrefixSupport.lean` | `96769da49e4b10fff8a47ababb707a0d7ea8e8de709fb490e16ad7bce526bb8c` |
| `lean-statements/NLA/Proofs/RA10/SelectedCompressionTail.lean` | `bf7df719a1e84abfc819df5e43a61ea2392529560ffda11a94fdde43f418033b` |
| `lean-statements/NLA/Proofs/RA10/SelectedProjectionIdempotent.lean` | `8ac0fb000300bca16bacdbefe1d0e8c4286418df8bc1c466081e6a1edf966a78` |
| `lean-statements/NLA/Proofs/RA10/SelectedProjectionRank.lean` | `71b13af889493c08dcadb56c749f049cfa34d939e602d8145c3a91de8ac15eb2` |
| `docs/lean/proofs/RA-10/RIDGE_COMPRESSION_POSITIVE_PART_PRE_REVIEW.md` | `ecbb548c34f50c6804e48c92ae6ff655ce99313f04858291dd83ca2d0cfe5d14` |

## Exact support identity

For any `n,k` with `k≤n`, let `P=selectedProjection k QAhat` from a supplied ordered PSD decomposition of `Ahat`. Its audited identities give `P=Pᵀ=P²`, `rank(P)=k`, and `tr P=k`. Let `C=P*A*P`, and take any ordered PSD spectral witness `(eigenvaluesC,QC)` of **this actual C**. No supplied decomposition of `A` is needed for this helper; the final Lemma 2 gate retains the original `(eigenvaluesA,QA)` separately. Fix `c>0`.

Then the exact positive-part trace identity is

```text
tr(hermitianPositivePart(c • P − C))
  = ∑_{i : Fin n, i.val<k} max(c−eigenvaluesC i,0).
```

The right side is exactly the source's `d=tr((cI_k−H)₊)` for `H=C|range(P)`: it includes the `k−rank(C)` zero eigenvalues **inside** `range(P)`, each contributing `c`, while the `n−k` dimensions in `ker(P)` contribute zero. The formula is basis independent for all tied eigenvalues and for an arbitrary supplied `QC`; in particular, the given zero eigenvectors of `QC` need not lie in `range(P)`.

This is an equality, not merely the already audited Eq. (11) upper bound. The earlier variational inequality cannot be reversed without the additional spectral support analysis below. The formula includes `k=0`, `k=n`, and `n=0` if mathematically meaningful; the final source application later uses `1≤k<n`. It imposes neither a gap nor invertibility of `C` or its restriction `H`.

## Proof plan and numerical checks

Let `J={i | 0<eigenvaluesC i}` and `r=|J|≤k`. Orderedness makes `J` a prefix; the audited tail theorem gives zero eigenvalues for `i.val≥k`. The audited positive-eigenvector support theorem puts each `QC` column with index in `J` in `range(P)`. Its orthogonal support projector `E=Σ_{i∈J}q_iq_iᵀ` therefore satisfies `PE=EP=E`; `P₀=P−E` is an orthogonal projector of trace `k−r`. Exact spectral reconstruction gives `C=Σ_{i∈J}h_iq_iq_iᵀ`, with `h_i=eigenvaluesC i`.

Consequently the orthogonal block decomposition of `cP−C` is

```text
Σ_{i∈J}(c−h_i) q_iq_iᵀ  +  cP₀  +  0 on ker(P).
```

Its positive part has trace `Σ_{i∈J}max(c−h_i,0)+c(k−r)`, exactly the stated first-`k` sum because all other selected eigenvalues are zero and `max(c−0,0)=c`. This argument preserves the actual supplied `QC` on positive eigenspaces and does not align its zero eigenvectors with `QAhat`.

At `n=2,k=1`, `A=diag(3,1)`, and `P` onto `(1,1)/sqrt(2)`, actual `C=2P`; with `c=3`, `cP−C=P` and both sides are `1`. In the rank-deficient selected case `C=0`, the identity reads `tr(cP)=ck`, also exact. If `k=0`, both sides are zero. These examples check the missing-zero-eigenvalue contribution and prevent treating `cP−C` as `cI−C` on the full space.

## Proposed sole public Lean signature

After independent mathematical/source review, a separate `NLA.Proofs.RA10.RidgeCompressionDefectSupport` module may expose:

```lean
namespace NLA.Proofs.RA10

theorem selectedCompression_defect_positivePart_trace_eq_sum {n k : ℕ}
    (hk : k ≤ n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC)
    {c : ℝ} (hc : 0 < c) :
    let P := selectedProjection k QAhat
    let C := P * A * P
    Matrix.trace (hermitianPositivePart (c • P - C)) =
      ∑ i : Fin n, if i.val < k then max (c - eigenvaluesC i) 0 else 0 := by
  ...

end NLA.Proofs.RA10
```

All trace and positive-part objects are the pinned frozen ones. Any private helper may use the same zero/positive spectral split. Do not use `sorry`, a new axiom, floating-point evaluation, or a weaker inequality to stand in for the exact identity. After implementation, direct pinned LeanCert kernel check, source freeze, separate imported exact-signature/axiom audit, and aggregate import are required. The full coefficient-two Lemma 2 estimate and frozen RA-10 Target remain open.
