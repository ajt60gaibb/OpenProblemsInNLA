# RA-10 selected support algebra for Equation (14)

**Status:** exact source-locked mathematical and matrix-order precontract for independent review. No Lean implementation or proof is claimed.

## Frozen sources and scope

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `lean-statements/NLA/Proofs/RA10/MatchedLeadingRidge.lean` | `6ee44a9e0f081b318a73aa97aa234ed37c596623c3d667875b1f461a63a0af31` |
| `lean-statements/NLA/Proofs/RA10/SelectedProjectionFunction.lean` | `78b15a4bcdcbbd0bebb87a6f64a8e99db062ecdd5d85a125b04be99b45b29dee` |
| `lean-statements/NLA/Proofs/RA10/RidgeResolventOpNormSelected.lean` | `845a5cdcc7eb79f87a76e66cdb4614207b82b74f1fb8bb4137e7806a6c8a18ef` |

The source Section 3 defines `B₀` in the **selected** eigenvectors of `B=Âₖ`, lets `P` project onto exactly those vectors, and sets `C=PAP`. Equation (14) uses `s(sI+B₀)⁻¹(B₀−C)(sI+C)⁻¹`. The sharp bound `1/(s+c)` from the reviewed operator-norm gate applies to `P(sI+B₀)⁻¹P`, **not** the full inverse. This algebra gate justifies inserting those two selected projectors in the left factor. It does not establish the nuclear ideal inequality.

## Exact mathematics

For arbitrary `n,k : ℕ`, two independent supplied ordered PSD decompositions of `A` and `Ahat`, and their actual bases `QA` and `QAhat`, use these exact local abbreviations:

```text
P  := selectedProjection k QAhat,
B₀ := FunctionTruncation k id eigenvaluesA QAhat,
C  := P A P,
D  := B₀−C.
```

The same frozen zero-based predicate `a.val<k` defines both `P` and `B₀`; no basis is reselected or reordered. Prove `P²=P` using the supplied `QAhat` orthonormality, then the exact support identities

```text
P B₀ P = B₀,
P C P = C,
P D P = D.
```

The first follows from the existing selected functional-calculus theorem applied to the matched leading-spectrum matrix; the second is only projector algebra with **this actual** `C=PAP`. The third is subtraction. Each identity holds even for tied/zero eigenvalues, `k=0`, `k=n`, `k>n`, and `n=0`; the final Target later uses `1≤k<n`.

For `s>0`, the source matched-spectrum gate proves `sI+B₀` is a unit, and its inverse is the supplied `QAhat` spectral reciprocal. Since `P` and `B₀` are diagonal in that same basis, `P` commutes with the actual `R_B₀=(sI+B₀)⁻¹`. Prove exactly

```text
P R_B₀ = R_B₀ P.
```

Then `D=PDP` gives the precise **noncommutative** insertion identity

```text
R_B₀ D R_C = (P R_B₀ P) D R_C,
where R_C=(sI+C)⁻¹ and C=PAP.
```

The equality makes no commutation claim between `B₀` and `C` or between `R_B₀` and `R_C`. The factor `s` in Equation (14) is retained by scalar multiplication of both sides. The only commutation is `P R_B₀=R_B₀ P`, justified by their common selected basis. Do **not** instantiate this theorem with an arbitrary PSD `C` from the earlier general product identity: the insertion requires the explicit compression equality `C=PAP` (or a separately proved support premise).

## Proposed exact Lean declarations

Use a new `NLA.Proofs.RA10.MatchedLeadingSupport` module. Let-bound expressions in the proposition are definitional abbreviations of the displayed frozen matrices, not new target objects.

```lean
namespace NLA.Proofs.RA10

theorem matchedLeading_supported {n k : ℕ}
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    let P := selectedProjection k QAhat
    let B₀ := NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat
    P * B₀ * P = B₀ := by
  ...

theorem selectedCompression_supported {n k : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    {Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesAhat : Fin n → ℝ}
    {QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    let P := selectedProjection k QAhat
    let C := P * A * P
    P * C * P = C := by
  ...

theorem matchedLeading_compressionDifference_supported {n k : ℕ}
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    let P := selectedProjection k QAhat
    let B₀ := NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat
    let C := P * A * P
    P * (B₀ - C) * P = B₀ - C := by
  ...

theorem matchedLeading_shiftInverse_commutes {n k : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    let P := selectedProjection k QAhat
    let B₀ := NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat
    P * (s • (1 : Matrix (Fin n) (Fin n) ℝ) + B₀)⁻¹ =
      (s • (1 : Matrix (Fin n) (Fin n) ℝ) + B₀)⁻¹ * P := by
  ...

theorem matchedLeading_leftResolvent_restriction {n k : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    let P := selectedProjection k QAhat
    let B₀ := NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat
    let C := P * A * P
    let D := B₀ - C
    let RB := (s • (1 : Matrix (Fin n) (Fin n) ℝ) + B₀)⁻¹
    let RC := (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹
    RB * D * RC = (P * RB * P) * D * RC := by
  ...

end NLA.Proofs.RA10
```

## Review and verification

Independent review must check the exact `C=PAP` source identity, the shared selected basis for `P,B₀` only, noncommutative multiplication order, that `PDP=D` truly permits the displayed insertion, and all empty/tie/zero cases. Implementation follows only after approval, with pinned Lean 4.33.1/LeanCert kernel checks, frozen-source imported exact-signature/axiom audit and aggregate import. The actual Equation (14) **nuclear norm inequality**, nuclear ideal property, ridge compression Lemma 2, min-max/eigenvalue perturbation bounds, operator-monotone integral representation and full RA-10 `Target` remain open.
