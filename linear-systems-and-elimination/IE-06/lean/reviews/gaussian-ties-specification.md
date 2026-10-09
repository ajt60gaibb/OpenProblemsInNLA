# Gaussian pivot-tie nullity: reviewed bounded implementation plan

Date: 2026-10-06. Author: mathematical-review agent. The coordinator reviewed
and approved the common-denominator polynomial plan before implementation.
No core definitions or stochastic axioms are to be added or replaced.

The final exact contracts are:

```lean
theorem gaussianMatrix_admissiblePath_unique_ae (n : ℕ) :
    ∀ᵐ A ∂ gaussianMatrix n, ∃! path : PivotPath n, AdmissiblePath A path

theorem gaussianMatrix_admissiblePath_eq_firstPath_ae (n : ℕ) :
    ∀ᵐ A ∂ gaussianMatrix n, ∀ path : PivotPath n,
      AdmissiblePath A path → path = firstPath A
```

A stronger intermediate assertion rules out equal absolute values between
any two distinct active pivot-column entries along every admissible path,
simultaneously over the finite path and index sets. This includes every
admissible tie choice. Dimension zero has a unique empty path.

For a fixed path and stage `k`, `ActivePrefix` means that each preceding chosen
row index is at least its stage index. `NonzeroPrefix` requires each preceding
pivot in the actual trajectory to be nonzero. Full admissibility implies both.
The polynomial nonvanishing claim is restricted to active prefixes; it is not
asserted for arbitrary invalid path maps.

Use polynomials in the actual `n²` flattened entry coordinates. Start with
common denominator `D₀ = 1` and matrix of numerators `N₀,ij = Xij`. At stage `k`,
swap the numerator rows exactly as the actual Schur update does. Writing `p`
for its pivot numerator, set

`Dₖ₊₁ = Dₖ p`,

`Nₖ₊₁,ij = Nsw,ij p − Nsw,ik Nsw,kj`

on the next active block and zero elsewhere. On a nonzero active prefix,
induction proves the evaluated denominator is nonzero and the actual
trajectory entries equal evaluated numerator divided by that denominator.

For distinct active rows `i,j`, the tie polynomial is
`Nₖ,ik² − Nₖ,jk²`. To prove it is nonzero, construct an input realizing a stage
`k` tail with entry `(i,k)` equal to one and all other entries zero. Realization
uses induction: prepend a pivot equal to one, with zero off-pivot row/column,
then undo the specified active row swap. The desired tail may be singular;
only the preceding pivots must be nonzero. At this witness the evaluated tie
polynomial equals the nonzero squared common denominator.

The already-proved atomless-product polynomial-null theorem and explicit
Gaussian vectorization map then show each fixed guarded tie event is null.
Finite intersections of almost-everywhere statements cover all paths, stages,
and row pairs with no positive failure-probability penalty. A deterministic
induction shows two admissible paths must choose the same row at each stage:
their maxima have equal magnitude, so distinct pivot indices would violate
the separation property. Gaussian nonsingularity and the existing exact
path-existence theorem supply existence almost everywhere. The canonical
first-available path then gives the selected-rule bridge.

This plan adds finite algebra and uses the existing generic polynomial-null
result. It requires neither an assumed conditional Gaussian theorem nor a
Schur-complement determinant/minor identity. Each resulting theorem must
compile with a kernel-trust assertion and permitted transitive axiom audit.
