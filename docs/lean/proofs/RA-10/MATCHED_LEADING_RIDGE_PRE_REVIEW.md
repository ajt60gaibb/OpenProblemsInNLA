# RA-10 matched leading-spectrum matrix and Equation (14) algebra

**Status:** source-locked mathematical/indexing and exact-signature precontract for independent review. No Lean implementation or proof is claimed.

## Frozen sources

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `lean-statements/NLA/Proofs/RA10/RidgeResolventProduct.lean` | `0e608459592be87ecbcd06d4e787b167352ef593392334447ce2aba237cc70b2` |

The source's Section 3 defines `B₀` in the **selected** eigenvectors of `B = Âₖ`, with eigenvalues `a₁,…,aₖ` from `A` and zero on the selected complement. Its Equation (14) uses `fₛ(B₀)−fₛ(C)` and the product `s(sI+B₀)⁻¹(B₀−C)(sI+C)⁻¹`. This gate identifies that exact matrix with the frozen truncation, then applies the independently reviewed noncommutative resolvent product identity. It does not assert Equation (14)'s nuclear-norm inequality or source Lemma 2.

## Exact mathematics and indexing

For arbitrary `n,k : ℕ`, retain both independently supplied ordered PSD decompositions `A, eigenvaluesA, QA` and `Ahat, eigenvaluesAhat, QAhat`. Define only as a local abbreviation

```text
B₀ := FunctionTruncation k id eigenvaluesA QAhat,
clipped(a) := if a.val < k then eigenvaluesA(a) else 0.
```

The index condition `a.val < k` is the frozen zero-based truncation, so it selects exactly source indices `1,…,k` when `k≤n`. Do not substitute `QA` for `QAhat`; `B₀` and `B` share the latter selected vectors, while `A` may have an unrelated basis. Ties, zero eigenvalues, `k=0`, `k=n`, `k>n`, and `n=0` require no exceptional convention: the same predicate and finite spectral sum apply.

Prove `B₀ = SpectralMatrix clipped QAhat` entrywise. Since `eigenvaluesA` is nonnegative and antitone, `clipped` is nonnegative and antitone even across the selected/complement boundary. The orthonormality is that of the **supplied** `QAhat`. Hence prove the complete frozen `OrderedPSDSpectralDecomposition B₀ clipped QAhat`, without selecting a replacement basis.

For `s>0`, the ridge atom `ridgeAtom s x=x/(s+x)` has exact value zero at zero. Thus

```text
FunctionMatrix (ridgeAtom s) clipped QAhat
  = FunctionTruncation k (ridgeAtom s) eigenvaluesA QAhat.
```

This identity depends on the value at zero; it is **not** claimed for arbitrary `f` with `f(0)>0`. Finally, for an independent supplied PSD spectral decomposition of `C`, use the exact *right-order* resolvent theorem with its first matrix `C` and second matrix `B₀` to prove

```text
FunctionTruncation k (ridgeAtom s) eigenvaluesA QAhat
  − FunctionMatrix (ridgeAtom s) eigenvaluesC QC
  = s • ((sI+B₀)⁻¹ · (B₀−C) · (sI+C)⁻¹).
```

This is source Equation (14)'s matrix equality before applying the nuclear ideal-property bound, with exact factor `s` and multiplication order. It remains valid if `C` is any supplied PSD matrix; later use will specialize `C=PAP` and establish its support separately. No commuting-basis, positive gap or strict-PSD hypothesis is introduced.

## Proposed exact Lean declarations

Use a new `NLA.Proofs.RA10.MatchedLeadingRidge` module. The three declarations below are the review target. Here `id` is written `fun t : ℝ => t` to make the frozen truncation's function explicit.

```lean
namespace NLA.Proofs.RA10

theorem matchedLeading_orderedPSD {n k : ℕ}
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat)
      (fun a : Fin n => if a.val < k then eigenvaluesA a else 0) QAhat := by
  ...

theorem matchedLeading_ridgeFunctionMatrix {n k : ℕ} {s : ℝ}
    (hs : 0 < s) (eigenvaluesA : Fin n → ℝ)
    (QAhat : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.FunctionMatrix (ridgeAtom s)
      (fun a : Fin n => if a.val < k then eigenvaluesA a else 0) QAhat =
    NLA.Statements.RA10.FunctionTruncation k (ridgeAtom s) eigenvaluesA QAhat := by
  ...

theorem matchedLeading_ridgeProduct_right {n k : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A Ahat C : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QA QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition C eigenvaluesC QC) :
    NLA.Statements.RA10.FunctionTruncation k (ridgeAtom s) eigenvaluesA QAhat -
      NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC =
      s • ((s • (1 : Matrix (Fin n) (Fin n) ℝ) +
        NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat)⁻¹ *
        (NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat - C) *
        (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹) := by
  ...

end NLA.Proofs.RA10
```

## Review and verification

Independent pre-review must check the cross-basis construction of `B₀`, the clipped sequence's antitone property at the cutoff, `ridgeAtom s 0=0`, the source's exact `B₀−C` orientation, all matrix multiplication order, and the empty/zero/tie cases. Implementation may be staged in separate modules after review, with direct pinned Lean 4.33.1 and LeanCert kernel checks and a frozen-source imported exact-signature/axiom audit. The full RA-10 `Target`, nuclear ideal inequality, min-max bounds, compression Lemma 2 and operator-monotone integral representation remain open.
