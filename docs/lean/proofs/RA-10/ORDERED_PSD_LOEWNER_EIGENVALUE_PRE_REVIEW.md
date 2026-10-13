# RA-10 ordered PSD eigenvalue comparison under the frozen matrix order

**Status:** source-locked mathematical and exact-signature precontract for independent review. No Lean implementation or proof is claimed. This is a generic min-max dependency toward the approved coefficient-one nuclear ideal inequality; it does not prove that inequality, source Equation (14), pinching, or the full `RA-10` Target.

## Source lock

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `docs/lean/proofs/RA-10/NUCLEAR_IDEAL_EQ14_PRE_REVIEW.md` | `77da0117b61b482c844382ab4893ad0553b48fce67a66d807a7f42809cdbd3ef` |
| `lean-statements/NLA/Proofs/RA10/OrderedSpectralRayleigh.lean` | `3a7c03df2db70a97f16fcf05a00585e3f25d10fc523c27f2a3c31a6f9c1a4fc8` |
| `lean-statements/NLA/Proofs/RA10/OrderedSpectralIntersection.lean` | `7f0b889dcc02b9d17ed8974fb639b313b6364615eeab3f0c3fb83446adec348d` |
| `lean-statements/NLA/Proofs/RA10/SelectedCompressionComparison.lean` | `0d9d37901de4cca6e48f40d5a73740093b5e60bc9a0b7113cc2189de85013741` |

## Exact mathematical statement

For every `n : ℕ`, real `n×n` matrices `G,H`, **arbitrary supplied** ordered PSD spectral decompositions `(g,QG)` of `G` and `(h,QH)` of `H` in the frozen `OrderedPSDSpectralDecomposition` sense, and the **frozen** real PSD predicate on the difference `G-H`, prove at every same zero-based `a : Fin n`:

```text
h(a) ≤ g(a).
```

The order premise is precisely `NLA.Statements.RA10.PositiveSemidefinite (G-H)`: both its symmetry conjunct and its nonnegative all-vector double quadratic sum are retained. There is no entrywise nonnegativity, simultaneous eigenbasis, commutation, spectral gap, strictly positive eigenvalue, or favorable basis choice. The coefficient is exactly one. Tied or zero eigenvalues and rank-deficient matrices are included. At `n=0` there is no `a`; at `n=1` the coordinate cuts are empty.

## Indexed min-max proof obligation

Use the audited intersection theorem with **`QC=QH`, `QA=QG`** at index `a`. It gives a nonzero `x` whose `QH` coordinates vanish strictly *after* `a` and whose `QG` coordinates vanish strictly *before* `a`. The audited Rayleigh bounds therefore have exactly these directions:

```text
h(a) · Σ_i x_i² ≤ xᵀ H x,
xᵀ G x ≤ g(a) · Σ_i x_i².
```

Expanding the frozen PSD quadratic form of `G-H` yields `xᵀH x ≤ xᵀG x`; no matrix inequality `G-H≥0` may be used without this exact bridge. The audited `nonzero_vector_sum_sq_pos` gives `Σ_i x_i²>0`, allowing cancellation of the **same** strictly positive factor. The chain is `h(a)Σx² ≤ xᵀHx ≤ xᵀGx ≤ g(a)Σx²`. The proof must preserve both supplied bases and the common index `a`, including repeated and zero eigenvalues.

## Proposed exact Lean declaration

After independent approval, implement in a separate `NLA.Proofs.RA10.OrderedPSDLoewnerEigenvalue` module, importing the audited Rayleigh/intersection and nonzero-square-sum facts:

```lean
namespace NLA.Proofs.RA10

theorem orderedPSDSpectral_eigenvalues_le_of_psd_sub {n : ℕ}
    {G H : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesG eigenvaluesH : Fin n → ℝ}
    {QG QH : Matrix (Fin n) (Fin n) ℝ}
    (hG : NLA.Statements.RA10.OrderedPSDSpectralDecomposition G eigenvaluesG QG)
    (hH : NLA.Statements.RA10.OrderedPSDSpectralDecomposition H eigenvaluesH QH)
    (hGH : NLA.Statements.RA10.PositiveSemidefinite (G - H))
    (a : Fin n) :
    eigenvaluesH a ≤ eigenvaluesG a := by
  ...

end NLA.Proofs.RA10
```

This is a generic PSD eigenvalue comparison. To derive the approved nuclear ideal inequality later, one must still prove the **actual Gram** order `(‖X‖² YᵀY)−(XY)ᵀ(XY)` is PSD under the scoped Euclidean L2 operator norm, construct or transfer ordered PSD decompositions of both Gram matrices, handle the scalar/square-root factors exactly, and sum the frozen singular values. None of those facts is smuggled into this theorem or assumed for the final Target.

## Review and verification gate

Independent pre-review must check the `G-H` orientation, Rayleigh lower/upper directions, strict index cuts and same-index pairing, actual frozen PSD predicate, coefficient one, ties/zeros, and `Fin 0`. Only after approval may the source be implemented. Direct pinned LeanCert kernel checks, frozen source SHA, and separate imported exact-signature/source/axiom audit are required before aggregate import. No `sorry`, `admit`, custom axiom, `native_decide`, unsafe declaration, or dimension-by-dimension computation.
