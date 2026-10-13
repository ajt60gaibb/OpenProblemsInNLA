# RA-10 Equation (14): actual compression and selected left resolvent

**Status:** source-locked mathematical, matrix-order and numerical precontract for independent review. No Lean implementation or nuclear norm estimate is claimed.

## Frozen sources and exact scope

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `lean-statements/NLA/Proofs/RA10/MatchedLeadingRidge.lean` | `6ee44a9e0f081b318a73aa97aa234ed37c596623c3d667875b1f461a63a0af31` |
| `lean-statements/NLA/Proofs/RA10/MatchedLeadingSupport.lean` | `426403f51df54d1ffa70f839b18921da2a9b63ea265112213e8c66d2530c0c18` |

The canonical source Section 3 sets `B₀` in the **selected** eigenvectors of `B=Âₖ`, `P` onto exactly those eigenvectors and `C=PAP`. Equation (14) begins with the exact matrix identity

```text
f_s(B₀)_P − f_s(C) = s (sI+B₀)⁻¹ (B₀−C) (sI+C)⁻¹.
```

The later numerical inequality is `‖f_s(B₀)_P−f_s(C)‖_* ≤ (1/(s+c)) ‖B₀−C‖_*`, where `c=a_k>0` in the source's one-based notation and is `eigenvaluesA j` for `j.val+1=k` in the frozen Lean statement. This gate proves the exact **operator equality with the support insertion**, not that nuclear inequality. The existing selected L2 operator-norm theorem supplies the sharp `1/(s+c)` factor only under `1≤k<n` and `c>0`; this gate itself needs no cutoff positivity beyond `s>0`.

## Mathematical and indexing contract

For arbitrary `n,k : ℕ`, `s>0`, independent supplied ordered PSD decompositions of `A` and `Ahat`, and the source-selected `QAhat`, let

```text
P  = selectedProjection k QAhat,
B₀ = FunctionTruncation k id eigenvaluesA QAhat,
C  = P A P,
RB = (sI+B₀)⁻¹,
RC = (sI+C)⁻¹.
```

Assume a supplied ordered PSD spectral decomposition **of this actual `C`** with eigenvalues `eigenvaluesC` and basis `QC`. The later gate proving existence of such a decomposition from the source's PSD hypotheses remains separate; this theorem must not substitute an arbitrary PSD `C` for `PAP`.

The existing `matchedLeading_ridgeProduct_right` theorem, instantiated with this `C`, gives

```text
FunctionTruncation k (ridgeAtom s) eigenvaluesA QAhat
  − FunctionMatrix (ridgeAtom s) eigenvaluesC QC
= s • (RB * (B₀−C) * RC).
```

The approved `matchedLeading_leftResolvent_restriction` theorem gives exactly

```text
RB * (B₀−C) * RC = (P*RB*P) * (B₀−C) * RC.
```

Thus the proposed conclusion retains the source factor `s`, puts both projectors on the **left** resolvent, and keeps the product order. It asserts no commutation of `B₀` with `C`, of `RB` with `RC`, or of `P` with `RC`. The selected `P` remains distinct from the `C` spectral basis `QC`, including ties and zero eigenvalues. The statement is valid for `k=0`, `k=n`, `k>n`, and `n=0`, conditional on its supplied decompositions. The full target later uses `1≤k<n`.

The corresponding frozen nuclear norm equality is only `NuclearNorm` applied to both sides of the matrix equality. It still requires a new kernel-proved nuclear ideal property and positivity/zero/spectral support facts to reach the numerical `1/(s+c)` bound. Avoid replacing `NuclearNorm` with the L2 operator norm or removing the factor `s`.

## Proposed exact Lean declarations

Use a new `NLA.Proofs.RA10.MatchedLeadingEq14Restricted` module. The `let` expressions are definitional abbreviations of the frozen objects, not alternate approximants.

```lean
namespace NLA.Proofs.RA10

theorem matchedLeading_ridgeProduct_restricted_right {n k : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QA QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC) :
    let P := selectedProjection k QAhat
    let B₀ := NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat
    let C := P * A * P
    let RB := (s • (1 : Matrix (Fin n) (Fin n) ℝ) + B₀)⁻¹
    let RC := (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹
    NLA.Statements.RA10.FunctionTruncation k (ridgeAtom s) eigenvaluesA QAhat -
      NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC =
        s • ((P * RB * P) * (B₀ - C) * RC) := by
  ...

theorem matchedLeading_ridgeProduct_restricted_nuclearNorm {n k : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QA QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC) :
    let P := selectedProjection k QAhat
    let B₀ := NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat
    let C := P * A * P
    let RB := (s • (1 : Matrix (Fin n) (Fin n) ℝ) + B₀)⁻¹
    let RC := (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹
    NLA.Statements.RA10.NuclearNorm
      (NLA.Statements.RA10.FunctionTruncation k (ridgeAtom s) eigenvaluesA QAhat -
        NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC) =
      NLA.Statements.RA10.NuclearNorm
        (s • ((P * RB * P) * (B₀ - C) * RC)) := by
  ...

end NLA.Proofs.RA10
```

## Review and verification boundary

Independent review must verify that `hC` is for the **actual source compression**, the selected and C bases remain independently supplied, source Equation (14)'s sign and multiplication order are exact, the factor `s` survives, and the nuclear norm equality is literal congruence only. After approval, implement in the new module, direct-check with pinned Lean 4.33.1/LeanCert kernel, freeze source SHA, and request imported exact-signature/source/axiom audit. The nuclear ideal bound, compression PSD spectral existence, source Lemma 2, pinching, eigenvalue perturbation, integral representation and full RA-10 `Target` remain open.
