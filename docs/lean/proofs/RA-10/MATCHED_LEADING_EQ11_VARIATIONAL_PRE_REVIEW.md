# RA-10 Eq. (11) matrix defect: coefficient-one variational upper bridge

**Status:** source-only revised mathematical/numerical/indexing precontract for independent review. This supplements `MATCHED_LEADING_EQ11_DEFECT_PRE_REVIEW.md` and leaves its already audited rank/tail and scalar-sum gates untouched. It replaces only the proposed two-sided spectral **equality** gate with the one-sided matrix inequality actually required to prove the original source Equation (11). No new Lean source has been implemented under this addendum.

## Frozen source and dependency locks

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `lean-statements/NLA/Proofs/RA10/SelectedCompressionTail.lean` | `bf7df719a1e84abfc819df5e43a61ea2392529560ffda11a94fdde43f418033b` |
| `lean-statements/NLA/Proofs/RA10/MatchedLeadingEq11Scalar.lean` | `34b6f57779a901dd2dcadf9148ef5c142c85c96558342b5bea13f975277b8168` |
| `lean-statements/NLA/Proofs/RA10/SelectedCompressionEigenvalue.lean` | `00c62e352faab14482b768bd95ceadbcb76ebb6a69e69ad2d6979376aa142d13` |
| `lean-statements/NLA/Proofs/RA10/HermitianPositivePart.lean` | `db272c38e076cd0e41a278d9a488f5aba5cab71f1104f146236f591a8ef3f6e8` |

All listed hashes are verified against the working tree. No IDs, README text, frozen Target, or supplied bases change.

## Exact finite-dimensional inequality

Keep the original `1≤k<n`, independent `hA` and `hAhat`, actual `P=selectedProjection k QAhat`, actual `C=PAP`, and zero-based `c=eigenvaluesA ⟨k−1,_⟩`. For an arbitrary supplied ordered PSD spectral witness `hC` of this exact `C`, write `h_i=eigenvaluesC i`. The audited rank/tail theorem says `h_i=0` for every `i.val≥k`; no compatibility of `QC` and `QAhat` is assumed.

The exact matrix positive part is already defined as `hermitianPositivePart`. Since `P=Pᵀ=P²`, `C=PCP`, and `c≥0`, `M=cP−C` is real Hermitian. The revised bridge claims the coefficient-one **upper bound**

```
trace (hermitianPositivePart (c • P − C))
  ≤ ∑ i : Fin n, if i.val < k then max(c − h_i,0) else 0.
```

This is sufficient, together with the separately audited scalar sum bound, to prove the **original Eq. (11)** `d≤L` with no changed source quantity or constant. The source's `d=trace((cI_k−H)_+)` is exactly the full-space trace on the left: `M` is zero on `range(P)⊥` and restricts to `cI_k−H` on `range(P)`. This block identification is a mathematical semantic fact to be stated explicitly; a final Lean theorem must use the full-space positive-part trace, and may not relabel the scalar sum as the matrix trace without proof.

## Proof plan avoiding zero-eigenbasis alignment

Let `J={i : Fin n | 0<h_i}`. By order and the audited tail-zero theorem, `J` is a prefix and `r=|J|≤k`. Let `q_i` be column `i` of the given `QC`, and form its positive spectral support projector

```
E = Σ_{i∈J} q_i q_iᵀ.
```

The audited positive-eigenvector support theorem gives `P q_i=q_i` for each `i∈J`, hence `PE=EP=E`. Therefore `P₀=P−E` is an orthogonal projection, `tr P₀=k−r`, and `C=Σ_{i∈J} h_i q_iq_iᵀ`. No given zero eigenvector is asserted to be in `range(P)`.

Let `R` be the orthogonal projector onto the positive eigenspace of `M=cP−C`, constructed from the same real Hermitian spectral theorem used in the frozen positive-part definition. Then

```
tr(M₊)=tr(RM).
```

For each `i∈J`, set `t_i=q_iᵀR q_i`. Orthogonal projection gives `0≤t_i≤1`. Also `tr(RP₀)≤tr P₀=k−r`: since `1−R` and `P₀` are orthogonal projections, `tr((1−R)P₀(1−R))≥0`, and trace cycling gives the bound. Thus, retaining the multiplication order,

```
tr(RM)
 = c tr(RP₀) + Σ_{i∈J}(c−h_i)t_i
 ≤ c(k−r) + Σ_{i∈J}max(c−h_i,0)
 = Σ_{i.val<k}max(c−h_i,0).
```

The middle inequality uses `c≥0` and `0≤t_i≤1`, each with coefficient one; the last equality uses exactly `k−r` zero eigenvalues inside the first `k` positions, including all ties at zero. `n=0` is covered by the generic projector lemmas, while the source-range theorem has no instance with `1≤k<n` in that dimension. The proof does not need `C≤A`, a false Loewner claim, nor any identification of `QC` with `QAhat`.

## Proposed replacement and final Lean signatures

The formerly proposed `matchedLeading_defect_positivePart_eq_sum` may remain open. The exact replacement is:

```lean
namespace NLA.Proofs.RA10

theorem matchedLeading_defect_positivePart_le_sum {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QA QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC) :
    let c := eigenvaluesA ⟨k - 1, by omega⟩
    let P := selectedProjection k QAhat
    let C := P * A * P
    Matrix.trace (hermitianPositivePart (c • P - C)) ≤
      ∑ i : Fin n, if i.val < k then max (c - eigenvaluesC i) 0 else 0 := by
  ...

theorem matchedLeading_defect_le_loss {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    let c := eigenvaluesA ⟨k - 1, by omega⟩
    let P := selectedProjection k QAhat
    let C := P * A * P
    let L := (∑ i : Fin n, if i.val < k then eigenvaluesA i else 0) - Matrix.trace C
    Matrix.trace (hermitianPositivePart (c • P - C)) ≤ L := by
  ...

end NLA.Proofs.RA10
```

All projector/variational helpers may be private. A new public helper must receive a separately frozen exact signature and independent pre-review before implementation. The full Lemma 2, Eqs. (12)–(17), and frozen RA-10 Target remain open.
