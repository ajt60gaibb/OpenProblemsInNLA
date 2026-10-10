# RA-10 exact nuclear triangle and orthogonal pinching gate

**Status:** source-locked mathematical and Lean-signature precontract for independent review. No Lean implementation or proof is claimed. The permanent `RA-10` ID, canonical README, frozen `NLA.Statements.RA10.Target`, and its quantifiers remain unchanged.

## Source lock and exact role

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `docs/lean/proofs/RA-10/CONSTANT_ELEVEN_TRANSFER_PRE_REVIEW.md` | `43ec3208c3177ff931289bc236f9afa32796c25be96fc07127027654f2623a92` |

The RA-10 solution's Equation (8) pinches the symmetric matrix `A−B₀` into the selected `P` and `I−P` blocks, using the fact that this operation cannot increase the nuclear norm. Equation (9) and later steps also use its triangle inequality. This contract proves these for the **literal frozen** `NuclearNorm M = ∑_{i:Fin n} (Matrix.toEuclideanLin M).singularValues i.val`; no trace, Frobenius, operator norm, or surrogate is substituted in a public conclusion.

## Exact matrix facts

For every `n : ℕ` and arbitrary real `n×n` matrices `M,N`, prove

```text
NuclearNorm (M+N) ≤ NuclearNorm M + NuclearNorm N.          (triangle)
```

No symmetry or PSD premise is needed; the theorem includes `n=0`, singular matrices, and all ranks. The exact singular-value sum is over `Fin n`, not over only the nonzero values or an asymptotic limit. A permissible proof route is the finite-dimensional real singular-value decomposition and dual characterization

```text
NuclearNorm M = max_{UᵀU=I} tr(UᵀM),
```

followed by the triangle inequality for each linear functional. Any such SVD/dual characterization must itself be kernel-proved from the pinned Mathlib definitions; it is not an axiom or new hypothesis on `M` or `N`. A projective tensor norm route is also valid if the exact equivalence to the frozen singular-value sum is proved. A read-only search of the pinned singular-values module found the definition and nonnegativity API but no ready-made nuclear triangle theorem, so this may require substantial new finite-dimensional linear algebra.

For every square real matrix `U` satisfying both `UᵀU=I` and `UUᵀ=I`, prove exact two-sided orthogonal conjugation invariance:

```text
NuclearNorm (U M Uᵀ) = NuclearNorm M.                        (orthogonal invariance)
```

The needed singular values are unchanged by left and right orthogonal maps. The two equations are the exact orthogonality condition for a square matrix; later `U=2P−I` satisfies both. The proof must not assume `M` symmetric or PSD. Also prove real homogeneity `NuclearNorm (t • M)=|t| NuclearNorm M`, at least for `t=1/2`, from the same frozen singular-value definition. These are independent kernel obligations, not imported as custom axioms.

For every real symmetric idempotent `P` (`Pᵀ=P`, `P²=P`) and every real matrix `M`, prove

```text
NuclearNorm (P M P + (I−P) M (I−P)) ≤ NuclearNorm M.         (pinching)
```

This is exactly the two-block pinching used on `M=A−B₀`; it does not presume a favorable eigenbasis or commutation. Put `U=2P−I`. Then `Uᵀ=U`, `U²=I`, and entrywise matrix algebra gives

```text
P M P + (I−P) M (I−P) = (M + U M U)/2.
```

Apply the **proved** triangle, homogeneity and orthogonal invariance to obtain the nonexpansive coefficient `1` exactly. The proof must also establish that the selected projection from any supplied `QAhat` is symmetric idempotent before applying this general gate in RA-10. That selected-projection bridge is a separate obligation; it cannot be installed as an additional final hypothesis. Repeated eigenvalues and selected zero eigenvalues cause no exception.

## Proposed exact Lean declarations

Implement in a separate `NLA.Proofs.RA10.NuclearPinching` module, importing the frozen RA-10 statement and approved RA-10 norm bridge. The public declarations should have these signatures (notation may be elaborated with explicit matrix types, but hypotheses and conclusions must be identical):

```lean
namespace NLA.Proofs.RA10

theorem nuclearNorm_add_le {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.NuclearNorm (M + N) ≤
      NLA.Statements.RA10.NuclearNorm M + NLA.Statements.RA10.NuclearNorm N := by
  ...

theorem nuclearNorm_smul {n : ℕ}
    (t : ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.NuclearNorm (t • M) =
      |t| * NLA.Statements.RA10.NuclearNorm M := by
  ...

theorem nuclearNorm_orthogonal_conj {n : ℕ}
    (U M : Matrix (Fin n) (Fin n) ℝ)
    (hleft : U.transpose * U = 1) (hright : U * U.transpose = 1) :
    NLA.Statements.RA10.NuclearNorm (U * M * U.transpose) =
      NLA.Statements.RA10.NuclearNorm M := by
  ...

theorem nuclearNorm_pinch_le {n : ℕ}
    (P M : Matrix (Fin n) (Fin n) ℝ)
    (hsym : P.transpose = P) (hid : P * P = P) :
    NLA.Statements.RA10.NuclearNorm
      (P * M * P + (1 - P) * M * (1 - P)) ≤
      NLA.Statements.RA10.NuclearNorm M := by
  ...

end NLA.Proofs.RA10
```

The pinching theorem's `n=0` instance is valid because all matrices are uniquely zero. Its hypotheses say only that `P` is an orthogonal projection; they add no PSD or spectral-gap restriction to the final target. Its coefficient is exactly `1`, with no dimension factor.

## Review and verification gate

Independent pre-review must check the source's pinching orientation and coefficient, exact frozen norm, matrix multiplication order, orthogonal involution algebra, all dimensions, and absence of hidden proof assumptions. Implementation may be split into smaller source-locked modules after this review, but every theorem must undergo its own frozen-source, exact-signature, pinned LeanCert kernel and axiom audit before aggregate import. If an SVD or dual characterization cannot be proved with pinned dependencies, report this gate open; do not add it as an axiom or treat a conditional variant as the frozen theorem.
