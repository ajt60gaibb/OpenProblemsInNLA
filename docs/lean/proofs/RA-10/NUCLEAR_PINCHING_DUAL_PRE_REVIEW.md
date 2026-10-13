# RA-10 nuclear pinching via an exact orthogonal trace duality

**Status:** source-locked mathematical, numerical, and public-signature precontract for independent review. No Lean implementation of these declarations is claimed. The permanent RA-10 ID, canonical README, frozen `NLA.Statements.RA10.Target`, and every original quantifier remain unchanged.

## Source and dependency locks

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `docs/lean/proofs/RA-10/NUCLEAR_PINCHING_GATE_PRE_REVIEW.md` | `23d850db3f312e04a30d732e1e9f030f04b80f5c7eff1584c4711a3aa435ffa1` |
| `lean-statements/NLA/Proofs/RA10/NuclearNormHomogeneity.lean` | `f3b7c30c5d04e63bf92596aef9f418a0f9a5b6a015439136e7823d35c4c23eca` |
| `lean-statements/NLA/Proofs/RA10/NuclearOrthogonalConjugation.lean` | `f56ca9699037e9e42b7590ea0efce71e792cebc8ece832eac1b57ae56a50ffe7` |
| `lean-statements/NLA/Proofs/RA10/PinchingReflection.lean` | `262f37c9ecb1a10bd551bf1600cc4f15c0bbd344577198a0f528b0cbd393d829` |
| Pinned Mathlib `Analysis/InnerProductSpace/SingularValues.lean` | `ce8193fcd5d226845a71f66b8ca7ad385358916a6e0e688745410ac412ed5c81` |
| Pinned Mathlib `Analysis/InnerProductSpace/PiL2.lean` | `1f9827b2db67213c725a2dcc3fec52a87772966d1fbd3fc6857a019dbd7a6053` |
| Pinned Mathlib `Analysis/InnerProductSpace/Spectrum.lean` | `f12ef613416053c759ef30179147744c64eeec90f7467644cb30e64d532d7aa6` |
| Pinned Mathlib `LinearAlgebra/Matrix/Trace.lean` | `8053b04dc1c67b3a7d14262acc43b574e521940085e031726947f3c2241b7a73` |

The source's Equation (8) pinches `A-B₀` into the selected `P` and `I-P` blocks and uses coefficient-one contraction of the **literal frozen** `NuclearNorm M = ∑ i : Fin n, (Matrix.toEuclideanLin M).singularValues i.val`. The earlier pinching contract approved the exact triangle, homogeneity, orthogonal invariance, and contraction. Homogeneity, orthogonal conjugation, and reflection algebra now have separate kernel-proved gates. This precontract identifies the missing sharp triangle route and then the exact contraction, without treating either as already proved.

## Exact dual mathematics

For arbitrary real square `M` and real orthogonal `U` (`UᵀU=UUᵀ=I`), define the ordinary real trace pairing `tr(UᵀM)`. The exact finite-dimensional dual formula is

```
tr(UᵀM) ≤ NuclearNorm M,
and there exists an orthogonal U with tr(UᵀM) = NuclearNorm M.
```

The right side is the frozen sum of **all `n` zero-based singular values**, with zero values retained. It is not the Euclidean operator norm, Frobenius norm, or a trace of `M` itself. The pairing uses `U.transpose * M` in that order. No symmetry, invertibility, rank, or positive-dimension premise is allowed.

A kernel proof can use the ordered orthonormal eigenbasis `vᵢ` of the actual Gram operator `MᵀM`. Its eigenvalues are precisely `σᵢ(M)^2` at the same `Fin n` index. Thus `‖Mvᵢ‖=σᵢ(M)`. Trace is invariant under this orthogonal change of basis, so

```
tr(UᵀM) = Σᵢ ⟨U vᵢ, M vᵢ⟩ ≤ Σᵢ σᵢ(M).
```

For attainment, on every index with `σᵢ>0`, set `wᵢ=Mvᵢ/σᵢ`. These `wᵢ` are orthonormal because the `vᵢ` diagonalize `MᵀM`. Extend them to an orthonormal basis of the same `n`-dimensional real space, retaining their original indices. The pinned `Orthonormal.exists_orthonormalBasis_extension_of_card_eq` theorem has exactly this fixed-index subset form; its hypotheses, including the cardinality equality and orthonormality of the restricted family, must be proved. An orthogonal `U` mapping each `vᵢ` to the corresponding `wᵢ` has `⟨Uvᵢ,Mvᵢ⟩=σᵢ` for positive indices, and the remaining terms are zero because `σᵢ=0` implies `Mvᵢ=0`. This also handles repeated positive singular values, all-zero `M`, rank deficiency, and `Fin 0`; for `Fin 0`, take `U=I` and both sides are empty sums equal to zero. The orthonormal extension and trace identity must themselves be proved in the pinned kernel, not assumed as external SVD facts.

Apply the attained `U` to `M+N`, then use linearity of trace and the upper bound separately on `M` and `N`. This gives the sharp triangle inequality with coefficient one. For symmetric idempotent `P`, the audited `reflection P=P+P-I` satisfies `Uᵀ=U`, `UᵀU=UUᵀ=I`, and `pinch P M=(1/2) • (M+UMU)`. The audited frozen homogeneity and two-sided orthogonal conjugation then give

```
NuclearNorm (pinch P M)
  ≤ (1/2) (NuclearNorm M + NuclearNorm (U M Uᵀ))
  = NuclearNorm M.
```

The factor is exactly `1/2` and the final contraction coefficient exactly `1`. This is valid for arbitrary nonsymmetric `M`, any projection rank including zero/full, and `n=0`. The source's actual selected projector has already been proved symmetric and idempotent from supplied `QAhat`; applying this generic bound adds no new final-target assumption.

## Proposed public Lean signatures

The first two declarations may be staged in `NLA.Proofs.RA10.NuclearTraceDual`; the triangle and pinching may be separate later modules. Matrix types may be elaborated explicitly, but hypotheses and conclusions must be identical:

```lean
namespace NLA.Proofs.RA10

theorem nuclearNorm_trace_orthogonal_le {n : ℕ}
    (U M : Matrix (Fin n) (Fin n) ℝ)
    (hleft : U.transpose * U = 1) (hright : U * U.transpose = 1) :
    Matrix.trace (U.transpose * M) ≤ NLA.Statements.RA10.NuclearNorm M := by
  ...

theorem nuclearNorm_trace_orthogonal_attains {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ,
      U.transpose * U = 1 ∧ U * U.transpose = 1 ∧
        Matrix.trace (U.transpose * M) = NLA.Statements.RA10.NuclearNorm M := by
  ...

theorem nuclearNorm_add_le {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.NuclearNorm (M + N) ≤
      NLA.Statements.RA10.NuclearNorm M + NLA.Statements.RA10.NuclearNorm N := by
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

Only these exact results may be claimed as they pass direct and independently imported LeanCert kernel audits. The trace upper bound alone does not prove triangle; attainment is indispensable. The pinching algebra alone does not prove contraction. Equation (8)'s full `e₀≥R+L` additionally needs nuclear additivity of orthogonal blocks and the PSD trace identity; this contract does not claim that conclusion, compression Lemma 2, or the full RA-10 `Target`.

## Independent review boundary

Check the ordinary trace pairing orientation, the same-index singular-value sum and Gram relation, the orthonormal completion for rank-deficient and zero matrices, the sharp coefficients, noncommutative reflection product, selected-projection bridge, and `Fin 0`. The pinned Mathlib singular-values file provides singular-value definitions and Gram links but no ready-made nuclear triangle theorem; all dual steps require kernel proofs with standard axioms only. No `sorry`, `admit`, `native_decide`, custom axioms, or weakened Target statement may enter the implementation.
