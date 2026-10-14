# RA-10 frozen PSD predicate to pinned Mathlib matrix PSD

**Status:** exact source-locked mathematical and numerical precontract for independent review. No Lean implementation or ordered spectral existence claim is made.

## Frozen sources and pinned library

| Source | SHA-256 or revision |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `lean-statements/NLA/Proofs/RA10/SelectedCompressionPSD.lean` | `ad69432066d88ff06bbdc68c1841498c4355eb5569cbb5c976745b98f90b9222` |
| pinned Mathlib in `lean-statements/lake-manifest.json` | `0df444a360eaa60ab8c11dca51a86af692955474` |

The source Section 3 uses `C=PAP≽0`. The approved SelectedCompressionPSD gate proves this in the **frozen** predicate. The pinned Mathlib real matrix spectral theorem and `Matrix.PosSemidef` lemmas require Mathlib's predicate. This gate proves their exact equivalence for every finite square real matrix, then supplies it for the actual source compression.

## Exact mathematical and numerical statement

For every `n : ℕ` and `M : Matrix (Fin n) (Fin n) ℝ`, the frozen `PositiveSemidefinite M` says both

```text
M_ij=M_ji for every i,j, and
Σ_i Σ_j x_i M_ij x_j ≥ 0 for every x : Fin n → ℝ.
```

The pinned `Matrix.PosSemidef M` says `M.IsHermitian` and nonnegative `star x ⬝ᵥ (M *ᵥ x)` for every real vector, as exposed by `Matrix.posSemidef_iff_dotProduct_mulVec`. Over `ℝ`, `star x=x`, `Mᴴ=Mᵀ`, and the finite sums are **exactly equal**:

```text
Σ_i Σ_j x_i M_ij x_j = x ⬝ᵥ (M *ᵥ x).
```

There is no change in strictness, normalization, dimension, or symmetry condition. The equivalence holds for `n=0` as well. Applying it to the approved source compression gives `Matrix.PosSemidef (P*A*P)` with `P=selectedProjection k QAhat`, under the original independently supplied decompositions of `A` and `Ahat`. This new proposition is a bridge to the library's real spectral theorem; it is not itself an ordered decomposition and asserts no eigenvalue comparison or nuclear estimate.

## Proposed exact Lean declarations

Use a new `NLA.Proofs.RA10.CustomPSDMathlibBridge` module with an explicit import of pinned `Mathlib.LinearAlgebra.Matrix.PosDef`. Retain the original source quantifiers and C rather than replacing it by arbitrary unrelated PSD data.

```lean
namespace NLA.Proofs.RA10

theorem sourcePositiveSemidefinite_iff_mathlibPosSemidef {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.PositiveSemidefinite M ↔ Matrix.PosSemidef M := by
  ...

theorem selectedCompression_mathlibPosSemidef {n k : ℕ}
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat) :
    Matrix.PosSemidef
      (selectedProjection k QAhat * A * selectedProjection k QAhat) := by
  ...

end NLA.Proofs.RA10
```

## Independent review boundary

Check the exact equivalence of the two symmetry conjuncts and of the two nonnegative quadratic forms in every finite dimension, including empty `Fin 0`. Check that the corollary applies only to the actual source `C=PAP`, preserving the supplied `QAhat`, and has no hidden full-target claim. After approval, implement with pinned Lean 4.33.1/LeanCert kernel, freeze SHA and request imported exact-signature/source/axiom audit. Constructing an ordered real spectral decomposition of C, min-max inequalities, source Lemma 2, nuclear ideal and pinching bounds, integral representation and full RA-10 Target remain open.
