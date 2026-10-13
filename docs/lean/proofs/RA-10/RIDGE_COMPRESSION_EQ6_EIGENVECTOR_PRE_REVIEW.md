# RA-10 Lemma 2, Equation (6): exact selected-compression eigenvector identity

**Status:** source-only mathematical, numerical, and Lean-signature precontract for independent review. Do not implement this new public theorem before that review approves these bytes. This is one identity for a positive eigenvector of the actual ridge-function difference; it does not prove source Equation (5), Equation (7), Lemma 2, or the frozen Target.

## Source locks

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `lean-statements/NLA/Proofs/RA10/SelectedProjectionBasic.lean` | `cfda9a5c7a4681542e47c967d5a4011e42b28f7cb3891bd3d192a7d336bea22b` |
| `lean-statements/NLA/Proofs/RA10/RidgeScalar.lean` | `5eab9a208a8fa9cb3f7c5cfa7ad0888ff3a0ac4c23f1236ee6166f6f1eaf792f` |
| `lean-statements/NLA/Proofs/RA10/RidgeResolventMatrix.lean` | `1523abd991863c75f890cac0abfcc905948716a0179e05985f16fdf6fed233c8` |
| `lean-statements/NLA/Proofs/RA10/RidgeResolventProduct.lean` | `0e608459592be87ecbcd06d4e787b167352ef593392334447ce2aba237cc70b2` |
| `lean-statements/NLA/Proofs/RA10/RidgeCompressionEq7Scalar.lean` | `de0382fa58336db491343e3e996d342bb6dc12029548b693608d0b0741a17e3f` |
| `docs/lean/proofs/RA-10/RIDGE_COMPRESSION_POSITIVE_PART_PRE_REVIEW.md` | `ecbb548c34f50c6804e48c92ae6ff655ce99313f04858291dd83ca2d0cfe5d14` |
| `docs/lean/proofs/RA-10/RIDGE_COMPRESSION_POSITIVE_PART_INDEPENDENT_PRE_REVIEW.md` | `5685fa2ac7172d312ebf6f5ffbb7da0371e9143ca82f596a4be397fe1d7e2479` |

## Exact source step and its full-space translation

The source starts with real `A ≽ 0`, orthogonal `P` of rank `k`, actual `C=PAP`, and ridge atoms `f_s(x)=x/(s+x)` for `s>0`. For a unit positive eigenvector `v=(u,w)` of `Z=f_s(C)−f_s(A)` with eigenvalue `λ>0`, it sets `μ=λ/(1+λ)` and obtains

```text
vᵀ(C−A)v = μs + μ(2−μ) uᵀH u.                (source Equation (6))
```

Here `H=C|range(P)`, `u=Pv`, and the zero complementary blocks of `C=PAP` give **exactly** `uᵀH u=vᵀCv`. The Lean theorem states this as `v ⬝ᵥ (C *ᵥ v)` over the original full space. It must establish that identification through the actual selected projector, rather than silently replacing an unrelated block matrix by `C`.

For the RA-10 application, `P=selectedProjection k QAhat`; `(eigenvaluesA,QA)` and `(eigenvaluesAhat,QAhat)` are independently supplied ordered PSD witnesses; and `(eigenvaluesC,QC)` is an arbitrary ordered PSD witness of that **same** `C`. `F_A` and `F_C` use the frozen `FunctionMatrix (ridgeAtom s)`, so the eigenpair equation has the source sign `F_C−F_A`. The full-space quadratic on the left has the source sign `C−A`. The vector is unit in the real Euclidean metric, expressed as `v ⬝ᵥ v=1`, not just nonzero.

The positive-tail application has cutoff `c=a_k=eigenvaluesA ⟨k−1,_⟩>0` with one-based `k`; neither `c` nor its positivity appears in source Equation (6). Therefore this exact Eq. (6) gate deliberately introduces no cutoff parameter or extra cutoff hypothesis. They enter the first inequality of Equation (7), where `H ≽ cI−Δ` is used. Likewise, source derives `λ<1` from ridge positivity; this identity needs only `λ>0`, so an external `λ<1` hypothesis is not added. These choices strengthen the local gate without changing the approved larger Lemma 2 signature.

## Sole proposed public Lean signature

Create a new, unimported `NLA.Proofs.RA10.RidgeCompressionEq6Eigenvector` module with exactly this public theorem:

```lean
namespace NLA.Proofs.RA10

theorem matchedLeading_ridge_positiveEigenvector_eq6 {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QA QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC)
    {s lam : ℝ} (hs : 0 < s) (hlam : 0 < lam)
    (v : Fin n → ℝ) (hvunit : v ⬝ᵥ v = 1)
    (hZv :
      (NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC -
        NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesA QA) *ᵥ v =
        lam • v) :
    let μ := lam / (1 + lam)
    let P := selectedProjection k QAhat
    let C := P * A * P
    v ⬝ᵥ ((C - A) *ᵥ v) =
      μ * s + μ * (2 - μ) * (v ⬝ᵥ (C *ᵥ v)) := by
  ...

end NLA.Proofs.RA10
```

The proof may use private helper lemmas and audited resolvent identities. It must derive the identity from the eigenpair, actual spectral witnesses, projector algebra, and unit norm. In particular, it may **not** assume source Equations (2), (4), or (6) as hypotheses; assume `H` invertible or `A` positive definite; align `QA`, `QAhat`, and `QC`; replace `C` by an unrelated PSD matrix; or reverse either difference. No new axiom, `sorry`, native decision procedure, or altered coefficient is permitted. Keep the source unimported and uncommitted until a separate final audit, with pinned LeanCert `kernel` checking and printed axioms.

## Exact numerical checks

1. Let `n=2`, `k=1`, `A=[[1,1],[1,1]]`, `Ahat=P=diag(1,0)`, `C=PAP=diag(1,0)`, and `s=1`. The ordered spectra are `a=(2,0)` and `h=(1,0)`, so the application cutoff is `c=a₁=2>0`. Independent orthonormal witnesses for `A`, `Ahat`, and `C` exist; no basis identification is needed. Directly, `F_A=A/3`, `F_C=diag(1/2,0)`, and `Z=[[1/6,−1/3],[−1/3,−1/3]]`. For unit `v=(-2,1)/√5`, `Zv=(1/3)v`, so `lam=1/3` and `μ=1/4`. The exact quadratics are `vᵀ(C−A)v=3/5` and `vᵀCv=4/5`; Equation (6) reads `3/5 = 1/4 + (1/4)(7/4)(4/5)`.
2. A singular selected compression with **positive** application cutoff is obtained at `n=4`, `k=2` by adjoining an omitted `A` eigenvalue `1` and a selected zero coordinate: `A=[[1,1,0,0],[1,1,0,0],[0,0,1,0],[0,0,0,0]]`, `P=diag(1,0,0,1)`, and `Ahat=P` with an ordered basis selecting coordinates `1,4` first. Then `C=diag(1,0,0,0)`, the ordered spectrum of `A` is `(2,1,0,0)`, `c=a₂=1>0`, and `H=C|range(P)=diag(1,0)` is singular. With `v=(-2,1,0,0)/√5`, `s=1`, and `lam=1/3`, the same exact identity is `3/5=1/4+(1/4)(7/4)(4/5)`.

Independent review must check the source Equation (6) translation, actual compression and basis quantifiers, both numerical witnesses, and whether the signature adds any unproved source step as a hypothesis before implementation begins.
