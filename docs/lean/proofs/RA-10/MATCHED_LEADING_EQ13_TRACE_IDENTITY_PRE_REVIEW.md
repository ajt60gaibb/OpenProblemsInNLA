# RA-10 Eq. (13): exact ridge excess / positive-part trace identity

**Status:** source-only mathematical, numerical, and indexing precontract for independent review. Do not implement its Lean theorem before approval. This is the first equality in source Equation (13), not its later inequality or the frozen `Target`.

## Frozen source and dependency locks

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `lean-statements/NLA/Proofs/RA10/HermitianPositivePart.lean` | `db272c38e076cd0e41a278d9a488f5aba5cab71f1104f146236f591a8ef3f6e8` |
| `lean-statements/NLA/Proofs/RA10/SelectedCompressionTail.lean` | `bf7df719a1e84abfc819df5e43a61ea2392529560ffda11a94fdde43f418033b` |
| `lean-statements/NLA/Proofs/RA10/MatchedLeadingEq12RidgeLoss.lean` | `da281781388a4c414491c18cd80c2f113c75bced4d6e82abd0a6e33b2c47037e` |

The ID, original README, frozen statement, and both supplied ordered bases stay unchanged. The all-singular-values `NuclearNorm`, exact `FunctionMatrix`, and exact matrix spectral positive part are the frozen definitions above. The Eq. (12) module already proves the separate coefficient-one `0≤L_s≤L/(s+c)` on the positive-cutoff branch; this gate does not assert that bound anew.

## Exact source quantities and finite identity

Retain `1≤k<n`, real `s>0`, and source positive cutoff `c=a_(k−1)>0`. Let `P=selectedProjection k QAhat`, `C=P*A*P`, and take **any** ordered PSD spectral witness `(eigenvaluesC,QC)` of this actual `C`. The original `(eigenvaluesA,QA)` and `(eigenvaluesAhat,QAhat)` remain independent and are both quantified. Put

```text
F_A = FunctionMatrix (ridgeAtom s) eigenvaluesA QA,
F_C = FunctionMatrix (ridgeAtom s) eigenvaluesC QC,
τ_s = ∑_{i.val≥k} ridgeAtom s (eigenvaluesA i),
L_s = ∑_{i.val<k} ridgeAtom s (eigenvaluesA i) − tr F_C.
```

Because the supplied decompositions reconstruct `A` and the **actual** `C`, `F_A` and `F_C` are the full matrix functions `f_s(A)` and `f_s(C)`. Since `ridgeAtom s 0=0`, the full-space `F_C` vanishes on `range(P)⊥`; its trace is exactly the source's `tr f_s(H)` even if the selected compression has rank below `k`. No zero-eigenvector alignment between `QC` and `QAhat` is assumed.

The required identity, with no additive loss or changed coefficient, is

```text
NuclearNorm(F_A − F_C) − τ_s
  = L_s + 2 * tr(hermitianPositivePart(F_C − F_A)).
```

The zero-based `i.val≥k` tail is exactly the one-based source `i>k`; every index belongs to exactly one of `i.val<k` or `k≤i.val`, including repeated or zero eigenvalues. The identity holds with empty tails; the source range excludes `n=0`, while any private generic trace lemma must also work in `Fin 0`.

## Coefficient-two derivation

Both `F_A` and `F_C` are real symmetric because each is a spectral sum in an orthonormal basis. Apply the already audited generic identity to the **ordered difference** `M=F_C−F_A`:

```text
NuclearNorm(M) = 2 tr(M₊) − tr M.
```

By exact negative-scalar homogeneity, `NuclearNorm(F_A−F_C)=NuclearNorm(M)`. Trace linearity yields `−tr M=tr F_A−tr F_C`. Exact spectral trace gives `tr F_A=Σ_i f_s(a_i)=Σ_{i.val<k}f_s(a_i)+τ_s`. Subtracting the same `τ_s` therefore gives the displayed equality. No positivity ordering between `F_A` and `F_C`, no Lemma 2 inequality, and no commutation of `A` and `C` is assumed. The trace-positive-part coefficient is exactly `2`; replacing it by `1` or changing `F_C−F_A` to the other orientation would be wrong.

For the next source inequality in Eq. (13), the separate unsolved Lemma 2 estimate must eventually bound this trace by `2/(s+c) * [tr((C−A)₊)+tr((cP−C)₊)]`, followed by audited Eqs. (10)–(12). This precontract proves only the equality above; it does not insert that missing estimate as an axiom or claim `g(2e_C+3L)` yet.

## Proposed sole public Lean signature

In a new `NLA.Proofs.RA10.MatchedLeadingEq13TraceIdentity` module, after independent review:

```lean
namespace NLA.Proofs.RA10

theorem matchedLeading_ridge_excess_positivePart_identity {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QA QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC)
    {s : ℝ} (hs : 0 < s)
    (hc : 0 < eigenvaluesA ⟨k - 1, by omega⟩) :
    let F_A := NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesA QA
    let F_C := NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC
    let τ_s := ∑ i : Fin n, if k ≤ i.val then ridgeAtom s (eigenvaluesA i) else 0
    let L_s := (∑ i : Fin n, if i.val < k then ridgeAtom s (eigenvaluesA i) else 0) -
      Matrix.trace F_C
    NLA.Statements.RA10.NuclearNorm (F_A - F_C) - τ_s =
      L_s + 2 * Matrix.trace (hermitianPositivePart (F_C - F_A)) := by
  ...

end NLA.Proofs.RA10
```

The `hc` hypothesis places this gate in the source positive-cutoff branch, even though the algebraic identity itself is valid for `c=0`; this does not add an assumption to the frozen final target. Private symmetry and trace lemmas may be used. Any additional public theorem requires its own exact pre-review. Direct pinned LeanCert-kernel checking, frozen SHA, separate imported exact-signature/source/axiom audit, and aggregate import must follow any implementation.
