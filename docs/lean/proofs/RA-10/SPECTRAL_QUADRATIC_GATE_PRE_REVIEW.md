# RA-10 Gate 1a: exact spectral quadratic form

**Status:** source-locked mathematical and Lean-signature precontract for independent review; no implementation or proof is claimed.

## Sources and scope

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `docs/lean/proofs/RA-10/CONSTANT_ELEVEN_TRANSFER_PRE_REVIEW.md` | `43ec3208c3177ff931289bc236f9afa32796c25be96fc07127027654f2623a92` |

This is the first narrow part of the approved spectral/nuclear bridge. It proves that the **literal frozen entrywise** `OrderedPSDSpectralDecomposition` entails the **literal frozen** `PositiveSemidefinite` predicate. It does not establish any nuclear-norm, functional-calculus, min-max, ridge, or constant-eleven inequality. No original statement, ID, basis choice, or quantifier changes.

## Exact mathematical content

For every `n : ℕ`, every real array `λ : Fin n → ℝ`, every real matrix `Q : Matrix (Fin n) (Fin n) ℝ`, and every `x : Fin n → ℝ`, set

`Sᵢⱼ = ∑_{a : Fin n} λₐ Qᵢₐ Qⱼₐ`, exactly the frozen `SpectralMatrix λ Q`. Prove the finite identity

```text
∑_{i : Fin n} ∑_{j : Fin n} xᵢ Sᵢⱼ xⱼ
  = ∑_{a : Fin n} λₐ (∑_{i : Fin n} xᵢ Qᵢₐ)^2.
```

Both sides are zero when `n=0`. The identity requires no positivity, sorting, or orthonormality assumption; it follows by finite sum rearrangement and distributivity. The index `a` runs over **all** `Fin n`, including zero eigenvalues. If every `λₐ≥0`, each right-hand summand is nonnegative. Also `Sᵢⱼ=Sⱼᵢ` for every `i,j` by commutativity of real multiplication. Thus if `A=S` via any frozen ordered PSD spectral decomposition, `A` is symmetric and has nonnegative quadratic form, exactly `PositiveSemidefinite A`. This handles arbitrary ties and any supplied basis without a spectral gap or invertibility hypothesis.

## Proposed exact Lean declarations

Put these in a separate `NLA.Proofs.RA10.SpectralQuadratic` module, importing only the frozen RA-10 statement and standard Mathlib facts:

```lean
namespace NLA.Proofs.RA10

theorem spectralMatrix_quadratic_form {n : ℕ}
    (eigenvalues : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n,
      x i * NLA.Statements.RA10.SpectralMatrix eigenvalues Q i j * x j) =
      ∑ a : Fin n, eigenvalues a * (∑ i : Fin n, x i * Q i a) ^ 2 := by
  ...

theorem orderedPSDSpectralDecomposition_positiveSemidefinite {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {eigenvalues : Fin n → ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ}
    (h : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvalues Q) :
    NLA.Statements.RA10.PositiveSemidefinite A := by
  ...

end NLA.Proofs.RA10
```

The first equality uses `x i * S i j * x j`, with the same multiplication order as the frozen PSD predicate. The second conclusion retains the **given** `A`, `eigenvalues`, and `Q`; no existential substitute decomposition appears. No `n≥2` is added because the internal identity and implication hold even for `n=0`, while the frozen `TransferBound` still quantifies over `n≥2`.

## Review and verification gate

Independent review must check the identity's finite-index rearrangement, the symmetry deduction, all dimensions including `n=0`, and exact agreement with the frozen predicates before coding. After approval, direct-build the separate module with pinned Lean 4.33.1 and `leancert.trust "kernel"`; independently recheck imported exact signatures, source hash, `#assert_trust kernel`, and `#print axioms`. Report this as a partial bridge only. The frozen `Target` remains open.
