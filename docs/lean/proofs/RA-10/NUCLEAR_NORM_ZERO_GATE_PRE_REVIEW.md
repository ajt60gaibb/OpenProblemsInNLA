# RA-10 Gate 1b: positivity and definiteness of the frozen nuclear norm

**Status:** mathematical and exact-signature precontract for independent review. No Lean implementation or proof is claimed here.

## Source lock

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `docs/lean/proofs/RA-10/CONSTANT_ELEVEN_TRANSFER_PRE_REVIEW.md` | `43ec3208c3177ff931289bc236f9afa32796c25be96fc07127027654f2623a92` |

This is a narrow second part of the approved Gate 1 spectral/nuclear bridge. It concerns the **actual frozen nuclear norm** `NLA.Statements.RA10.NuclearNorm`, whose sum contains exactly `n` singular values of `Matrix.toEuclideanLin M`. It neither proves nor assumes a trace surrogate, positivity of the input matrix, an eigenbasis, or any claim about `TransferBound 11`.

## Exact mathematical content and indexing

For every `n : ℕ` and every real `n×n` matrix `M`, prove

```text
0 ≤ NuclearNorm M,
NuclearNorm M = 0 ↔ M = 0.
```

The forward nonnegativity is a finite sum of nonnegative singular values. For definiteness, if the finite sum is zero, each term `singularValues i.val` with `i : Fin n` is zero. Mathlib's `singularValues_of_finrank_le` shows every term at a natural index `j≥n` is zero, because the Euclidean domain has real dimension exactly `n`; hence the complete finitely supported singular-value sequence is zero. Mathlib's `LinearMap.singularValues_eq_zero_iff` makes `Matrix.toEuclideanLin M` the zero linear map, and injectivity of the matrix-to-Euclidean-linear-map equivalence gives `M=0`. Conversely the zero matrix has zero map and zero singular values. The `n=0` case is genuine: the sum is empty and every `Fin 0` matrix is zero, so the equivalence remains valid. No ordering or positive eigenvalues are required, and the case `M=A−B` in the zero-tail branch follows without silently replacing the frozen norm.

## Proposed exact Lean declarations

Use a separate module `NLA.Proofs.RA10.NuclearNormZero`, importing the frozen RA-10 statement and standard Mathlib only:

```lean
namespace NLA.Proofs.RA10

theorem nuclearNorm_nonneg {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ NLA.Statements.RA10.NuclearNorm M := by
  ...

theorem nuclearNorm_eq_zero_iff {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.NuclearNorm M = 0 ↔ M = 0 := by
  ...

end NLA.Proofs.RA10
```

The conclusion is equality of the original matrix `M`, not equality of a replacement operator or a restricted class of PSD matrices. The definition of `NuclearNorm` and all its indices remain frozen. This gate is partial: nuclear triangle inequality, pinching, spectral perturbation and the constant-eleven transfer remain open.

## Review and verification

Independent pre-review must check the `Fin n` versus `ℕ` singular-value indexing, Euclidean dimension `n`, exact `n=0` behavior, and use of the real matrix-to-linear-map equivalence. Implement only after approval. Then direct-build with pinned Lean 4.33.1 in LeanCert kernel mode and freeze source for imported exact-signature/axiom review before aggregate import.
