# RA-10 exact ridge resolvent matrix bridge

**Status:** source-locked mathematical and exact-signature precontract for independent review. No Lean implementation or proof is claimed.

## Source lock and role

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `docs/lean/proofs/RA-10/CONSTANT_ELEVEN_TRANSFER_PRE_REVIEW.md` | `43ec3208c3177ff931289bc236f9afa32796c25be96fc07127027654f2623a92` |
| `docs/lean/proofs/RA-10/RIDGE_SCALAR_GATE_PRE_REVIEW.md` | `325fc8c9a9e32c35aec0e29d04b770891094bb9477e868697833e337dbc122e7` |

The source's Lemma 2 proof begins with the exact noncommutative identity

```text
fₛ(C)−fₛ(A)=s[(sI+A)⁻¹−(sI+C)⁻¹],
fₛ(x)=x/(s+x), s>0.
```

This gate proves the identity for the **frozen** `FunctionMatrix` and every supplied ordered PSD eigendecomposition, without assuming `A` and `C` commute or have positive eigenvalues. It does not prove the source's compression inequality (1), any nuclear-norm estimate, or `TransferBound 11`. The literal real scalar factor is `s`, not `1/s` or a numerical approximation.

## Exact finite-dimensional mathematics

For any `n : ℕ`, any real `A` with frozen `OrderedPSDSpectralDecomposition A eigenvalues Q`, and any `s>0`, all `s+eigenvalues a` are positive. Let `R=FunctionMatrix (fun x => 1/(s+x)) eigenvalues Q`. Show

```text
(sI+A) R = I,        R (sI+A)=I,
R=(sI+A)⁻¹.
```

Here the matrix inverse is Mathlib's actual inverse of the square real matrix. Derive the identities by the supplied `QᵀQ=I` and square-matrix completeness `QQᵀ=I`, the frozen spectral reconstruction `A=Q diag(eigenvalues) Qᵀ`, and the scalar equality `(s+x)(1/(s+x))=1` at every nonnegative eigenvalue. This includes zero eigenvalues and the unique `n=0` matrix. No positive-definite assumption on `A` is added; the shift `sI` alone makes the inverse valid.

For every such decomposition, prove the exact frozen ridge functional-calculus identity

```text
FunctionMatrix (ridgeAtom s) eigenvalues Q
  = I − s • (sI+A)⁻¹.
```

The scalar identity is `x/(s+x)=1−s/(s+x)` for every `x≥0`; the constant-one spectral matrix is exactly `I` because `QQᵀ=I`. `ridgeAtom` is the previously reviewed public definition `x/(s+x)`; negative inputs of an admissible function are irrelevant to this spectral evaluation.

For any two PSD matrices `A,C` with independent **supplied** decompositions, subtract the two identities and prove

```text
FunctionMatrix (ridgeAtom s) eigenvaluesC QC
  − FunctionMatrix (ridgeAtom s) eigenvaluesA QA
    = s • ((sI+A)⁻¹ − (sI+C)⁻¹).
```

This is the exact orientation in the source's Lemma 2. It is valid for arbitrary relative eigenspaces, tied eigenvalues, singular matrices, and `n=0`. Later setting `C=PAP` requires proving its own frozen ordered PSD decomposition or a basis-independent matrix functional calculus bridge; this theorem does not silently assume one.

## Proposed exact Lean declarations

Use a separate `NLA.Proofs.RA10.RidgeResolventMatrix` module, importing the frozen statement and the reviewed `RidgeScalar` definition. `I` below is the actual matrix `1`, and `sI` is `(s • (1 : Matrix (Fin n) (Fin n) ℝ))`:

```lean
namespace NLA.Proofs.RA10

theorem spectralShift_inverse {n : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (h : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvalues Q) :
    NLA.Statements.RA10.FunctionMatrix (fun x => 1 / (s + x)) eigenvalues Q =
      (s • (1 : Matrix (Fin n) (Fin n) ℝ) + A)⁻¹ := by
  ...

theorem ridgeFunctionMatrix_eq_resolvent {n : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (h : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvalues Q) :
    NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvalues Q =
      1 - s • (s • (1 : Matrix (Fin n) (Fin n) ℝ) + A)⁻¹ := by
  ...

theorem ridgeFunctionMatrix_sub {n : ℕ} {s : ℝ}
    (hs : 0 < s)
    {A C : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesC : Fin n → ℝ}
    {QA QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition C eigenvaluesC QC) :
    NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC -
      NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesA QA =
      s • ((s • (1 : Matrix (Fin n) (Fin n) ℝ) + A)⁻¹ -
        (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹) := by
  ...

end NLA.Proofs.RA10
```

The first theorem's proof must establish both left and right inverse identities internally, or use a kernel theorem that turns one into the actual matrix inverse for square real matrices. The **public** equality is to the actual inverse, not merely to an arbitrary right inverse. All three theorems keep the complete frozen matrix/eigenbasis arguments and add only `s>0`, which is the source's ridge-atom domain.

## Review and verification

Independent pre-review must check the resolvent subtraction orientation, the scalar `s` factor, diagonal/inverse formula, zero/tie cases, `n=0`, and absence of commutation or a hidden positive-definiteness premise. Only after approval implement, direct-build with pinned Lean 4.33.1/LeanCert kernel mode, freeze source, and independently audit exact imported signatures and axioms before aggregate import. The full matrix ridge compression and RA-10 Target remain open.
