# RA-10 exact ridge resolvent Loewner factor bounds

**Status:** source-locked mathematical/indexing/numerical precontract for independent review. No Lean implementation or proof is claimed.

## Frozen sources and source location

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `lean-statements/NLA/Proofs/RA10/SpectralQuadratic.lean` | `23e82984e32c8724fda21446037db91ca0180f52d41602dde086d16a1f954eae` |
| `lean-statements/NLA/Proofs/RA10/SelectedProjectionFunction.lean` | `78b15a4bcdcbbd0bebb87a6f64a8e99db062ecdd5d85a125b04be99b45b29dee` |
| `lean-statements/NLA/Proofs/RA10/RidgeShiftInverse.lean` | `db487f99898c55bd9958b19b2cfdd576342a36fdb21ec7f6269954309bac77e0` |
| `lean-statements/NLA/Proofs/RA10/MatchedLeadingRidge.lean` | `6ee44a9e0f081b318a73aa97aa234ed37c596623c3d667875b1f461a63a0af31` |

The source's Equation (14) applies the ideal property of the nuclear norm to the already proved exact matrix product `s(sI+B₀)⁻¹(B₀−C)(sI+C)⁻¹`. It states that the two resolvent factors have operator norms at most `1/(s+c)` on `range(P)` and `1/s`, respectively, where `c=a_k` in the source's one-based indexing. This gate proves the corresponding **exact Loewner bounds** in the frozen real-matrix PSD predicate. Conversion to operator norms and the nuclear ideal inequality are separate open dependencies.

## Exact mathematics and indexing

For every supplied ordered PSD decomposition `A,eigenvaluesA,QA` and `s>0`, put `R_A=(sI+A)⁻¹`. Since each eigenvalue of `R_A` is `1/(s+a_i)` with `a_i≥0`, prove exactly

```text
0 ≼ R_A ≼ (1/s) I.
```

Both claims use the frozen `PositiveSemidefinite` predicate, including its symmetry conjunct. The upper difference is `(1/s)I−R_A`, and the scalar coefficient is exactly `1/s−1/(s+a_i)=a_i/[s(s+a_i)]≥0`. The supplied eigenbasis remains fixed; zero eigenvalues, ties and `n=0` work without extra assumptions.

For the selected factor retain the two independent supplied decompositions of `A` and `Ahat`, the **selected** `QAhat`, and the frozen `B₀=FunctionTruncation k id eigenvaluesA QAhat` and `P=selectedProjection k QAhat`. In the source branch `1≤k<n`, let `j : Fin n` be the unique index satisfying `j.val+1=k`; then `c=eigenvaluesA j` is exactly the source's `a_k` (Lean's zero-based `a_(k−1)`). The cutoff witness exists under `1≤k<n`; `k=0` is outside this branch and outside the frozen Target range. This gate explicitly proves witness existence. No `Fin` modulo wraparound or substituted eigenbasis is allowed.

For all `a.val<k`, `a≤j`, so antitonicity gives `a_a≥c≥0`. Consequently, for `s>0`,

```text
0 ≼ P R_B₀ P ≼ [1/(s+c)] P.
```

On selected coordinates, the upper difference has exact coefficient

```text
1/(s+c) − 1/(s+a_a) = (a_a−c)/[(s+c)(s+a_a)] ≥ 0;
```

on the complementary coordinates it is zero after the `P` sandwich. This retains the **sharp** source constant `1/(s+c)`, including equality when `a_a=c`. The `c=0` case remains valid even though source Section 3 later assumes `τ>0` and hence `c>0`. The statement is about full `n×n` matrices and does not assume `B₀` and `C` commute.

## Proposed exact Lean declarations

Use a new `NLA.Proofs.RA10.RidgeResolventLoewner` module, possibly staged in separate named modules if needed. The exact declarations to review are:

```lean
namespace NLA.Proofs.RA10

theorem spectralShift_resolvent_nonnegative {n : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (h : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvalues Q) :
    NLA.Statements.RA10.PositiveSemidefinite
      ((s • (1 : Matrix (Fin n) (Fin n) ℝ) + A)⁻¹) := by
  ...

theorem spectralShift_resolvent_upperBound {n : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (h : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvalues Q) :
    NLA.Statements.RA10.PositiveSemidefinite
      ((1 / s) • (1 : Matrix (Fin n) (Fin n) ℝ) -
        (s • (1 : Matrix (Fin n) (Fin n) ℝ) + A)⁻¹) := by
  ...

theorem selectedCutoffIndex_exists {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n) :
    ∃ j : Fin n, j.val + 1 = k := by
  ...

theorem matchedLeading_selectedResolvent_nonnegative {n k : ℕ} {s : ℝ}
    (hs : 0 < s) (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (j : Fin n) (hj : j.val + 1 = k) :
    NLA.Statements.RA10.PositiveSemidefinite
      (selectedProjection k QAhat *
        (s • (1 : Matrix (Fin n) (Fin n) ℝ) +
          NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat)⁻¹ *
        selectedProjection k QAhat) := by
  ...

theorem matchedLeading_selectedResolvent_upperBound {n k : ℕ} {s : ℝ}
    (hs : 0 < s) (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (j : Fin n) (hj : j.val + 1 = k) :
    NLA.Statements.RA10.PositiveSemidefinite
      ((1 / (s + eigenvaluesA j)) • selectedProjection k QAhat -
        selectedProjection k QAhat *
          (s • (1 : Matrix (Fin n) (Fin n) ℝ) +
            NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat)⁻¹ *
          selectedProjection k QAhat) := by
  ...

end NLA.Proofs.RA10
```

The `j,hj` arguments state the exact zero-based cutoff without relying on a total modular `Fin.ofNat`; `selectedCutoffIndex_exists` supplies them from the frozen `1≤k<n` domain. The lower selected bound includes `hk,hkn,j,hj` to keep exactly the same source branch, even though its algebraic content holds more generally.

## Review and verification

Independent review must check both denominators, the scalar sign, the selected projector's orthogonality/support, zero-based cutoff, the complete symmetry and quadratic conditions in `PositiveSemidefinite`, and empty/tied/zero spectra. Implementation follows only after approval, with direct pinned Lean 4.33.1/LeanCert kernel checks, frozen-source imported exact-signature/axiom audit and aggregate import. No operator-norm conversion, nuclear ideal bound, min-max comparison, Lemma 2, integral representation or full RA-10 `Target` is claimed.
