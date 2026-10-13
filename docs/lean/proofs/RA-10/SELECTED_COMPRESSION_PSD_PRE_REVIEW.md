# RA-10 selected compression is positive semidefinite

**Status:** exact source-locked mathematical/indexing precontract for independent review. No Lean implementation or ordered spectral existence proof is claimed.

## Frozen source and dependency

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `lean-statements/NLA/Proofs/RA10/SpectralQuadratic.lean` | `23e82984e32c8724fda21446037db91ca0180f52d41602dde086d16a1f954eae` |
| `lean-statements/NLA/Proofs/RA10/SelectedProjectionBasic.lean` | `cfda9a5c7a4681542e47c967d5a4011e42b28f7cb3891bd3d192a7d336bea22b` |

Source Section 3 sets `C=PAP` for the projection `P` onto exactly the first `k` **supplied** eigenvectors of `Ahat`. It uses `C≽0` to apply the ridge resolvent argument and the compression eigenvalue bounds. The reviewed restricted Equation (14) equality currently accepts a supplied ordered PSD decomposition `hC` **of this actual C**. This gate establishes the concrete PSD condition on C, a necessary precursor to constructing such a decomposition. It neither asserts nor assumes existence of the ordered decomposition.

## Exact mathematics

For arbitrary `n,k : ℕ`, two independent ordered PSD spectral decompositions of `A` and `Ahat`, and the actual selected projection `P=selectedProjection k QAhat`, set `C=PAP`. The approved `selectedProjection_transpose` states `Pᵀ=P` even with zero/tied eigenvalues or out-of-range `k`. The approved `orderedPSDSpectralDecomposition_positiveSemidefinite` states `Aᵀ=A` and

```text
xᵀ A x = Σ_i Σ_j x_i A_ij x_j ≥ 0.
```

For every concrete `x : Fin n → ℝ`, set `y_i = Σ_j P_ij x_j` (the actual `P.mulVec x`). Then the exact finite-index identity is

```text
Σ_i Σ_j x_i C_ij x_j = Σ_i Σ_j y_i A_ij y_j.
```

The equality uses `Pᵀ=P` and **both** factors in `C=PAP`; no matrix ordering is inferred from entries. Therefore the left sum is nonnegative. Also `Cᵀ=Pᵀ Aᵀ Pᵀ=C`. These prove the frozen `NLA.Statements.RA10.PositiveSemidefinite C`, which explicitly requires symmetry and the quadratic inequality. The theorem is valid for `n=0`, `k=0`, `k=n`, `k>n`, zero eigenvalues and tied eigenvalues. The target range `1≤k<n` is not needed for this PSD gate.

This is a **0 lower bound** on a quadratic form, not an L2 operator norm or nuclear norm inequality. No `NuclearNorm` occurrence is replaced or weakened. The later ordered decomposition existence theorem must preserve the actual C and an independently chosen basis `QC`, then the source's min-max comparison `h_i≤a_i` and nuclear steps remain separate.

## Proposed exact Lean declarations

Use a new `NLA.Proofs.RA10.SelectedCompressionPSD` module. `Matrix.mulVec` is the finite sum `fun i => Σ_j P i j * x j` over `Fin n`. The first theorem is the full exact quadratic equality; the second is the source C's frozen PSD proposition.

```lean
namespace NLA.Proofs.RA10

theorem selectedCompression_quadratic_form {n k : ℕ}
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesAhat : Fin n → ℝ}
    {QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (x : Fin n → ℝ) :
    let P := selectedProjection k QAhat
    let C := P * A * P
    let y := P *ᵥ x
    (∑ i : Fin n, ∑ j : Fin n, x i * C i j * x j) =
      ∑ i : Fin n, ∑ j : Fin n, y i * A i j * y j := by
  ...

theorem selectedCompression_positiveSemidefinite {n k : ℕ}
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    NLA.Statements.RA10.PositiveSemidefinite
      (selectedProjection k QAhat * A * selectedProjection k QAhat) := by
  ...

end NLA.Proofs.RA10
```

## Independent review boundary

Review the exact source identity `C=PAP`, matrix multiplication order, `P` symmetry from supplied `QAhat`, the finite-index `mulVec` orientation, both conjuncts of the frozen PSD predicate, and all empty/tie/zero cases. Do not infer an ordered `hC` merely from PSD without proving a sorted real spectral theorem bridge. After approval, direct-check with pinned Lean 4.33.1/LeanCert kernel and freeze for an imported exact-signature/source/axiom audit. Equation (14)'s nuclear ideal inequality, ordered hC existence, min-max, pinching, ridge compression Lemma 2, integral representation and the complete RA-10 Target remain open.
