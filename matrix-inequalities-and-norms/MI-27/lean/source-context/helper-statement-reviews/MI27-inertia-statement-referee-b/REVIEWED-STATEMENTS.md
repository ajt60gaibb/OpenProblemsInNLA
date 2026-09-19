# MI27 C11: smallest independent algebraic bridge

Source-planning note by `/root/nr04_mf14_final_referee_a`, 2026-09-19.
No proof body is supplied or assumed. These are proposed independent helper
interfaces for root review or assignment to another source author, not
additional hypotheses on the frozen C11 target.

The common definition is now in the passed module `NLA.MI27.NegativeCount`,
source SHA256 `4882ae49e95e65293b29c2f2e47281f39de02ce1d045093eca8f6e55867e7713`:

```lean
def c11_negativeCount {n : ℕ} (M : Mat n) : ℝ :=
  trR (cfc (fun x : ℝ => if x < 0 then 1 else 0) M)
```

The previously reviewed full inertia interface is:

```lean
lemma c11_negativeCount_congruence {n : ℕ} (hn : 1 ≤ n) (M S : Mat n)
    (hM : M.IsHermitian) (hS : IsUnit S) :
    c11_negativeCount (Sᴴ * M * S) = c11_negativeCount M
```

The useful reduction is to a one-sided result for **arbitrary** S. No
invertibility of S is needed for this inequality:

```lean
lemma c11_negativeCount_congruence_le {n : ℕ} (hn : 1 ≤ n) (M S : Mat n)
    (hM : M.IsHermitian) :
    c11_negativeCount (Sᴴ * M * S) ≤ c11_negativeCount M
```

For invertible S, apply the same inequality to N=Sᴴ*M*S and S inverse;
matrix inverse identities reduce that reversed congruence to M. This gives
equality by antisymmetry and includes singular M without any perturbation.

## Smallest dimension lemma

The dimension argument itself can be separated completely from Hermitian
spectral calculus. A rectangular matrix transports one weighted sum of
complex squared moduli to another. Its number of negative input weights
cannot exceed the number of negative output weights:

```lean
lemma c11_negative_weights_card_le {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (T : Matrix (Fin m) (Fin n) ℂ)
    (hform : ∀ v : Fin n → ℂ,
      (∑ j : Fin n, b j * Complex.normSq (v j)) =
        ∑ i : Fin m, a i * Complex.normSq ((T *ᵥ v) i)) :
    Fintype.card {j : Fin n // b j < 0} ≤
      Fintype.card {i : Fin m // a i < 0}
```

This core statement includes m=0 or n=0 and arbitrary zero/repeated weights.
It needs no ordered structure on complex scalars and no realification.
The hypothesis is the concrete transported quadratic-form equality, not an
assumed inertia conclusion.

To prove it, extend a vector on the negative b-coordinates by zero to all
Fin n. Apply T, then restrict to the negative a-coordinates. This gives a
complex linear map between function spaces indexed by the two negative
coordinate subtypes. If its image is zero, the right weighted sum is
nonnegative: negative a-coordinates vanish, and the other a-weights are
nonnegative. A nonzero input has strictly negative left weighted sum,
since all its supported b-weights are strictly negative and at least one
Complex.normSq is positive. The equality hform forces the input to be zero.
The map is injective, so `LinearMap.finrank_le_finrank_of_injective`, together
with the finrank of a finite function space, gives the cardinal inequality.

For the matrix bridge set N=Sᴴ*M*S, let U and V be the separate eigenvector
unitaries of M and N, and take T=Uᴴ*S*V. The two spectral decompositions and
ordinary star/mulVec identities establish hform. The existing count formula
`c11_negativeCount_spectral` turns both finite negative-coordinate counts
into the corresponding real-valued CFC traces.

An independently useful spectral interface, if not proved locally inside
the matrix bridge, is:

```lean
lemma c11_hermitian_quadratic_spectral {n : ℕ} (M : Mat n)
    (hM : M.IsHermitian) (v : Fin n → ℂ) :
    (star v ⬝ᵥ (M *ᵥ v)).re =
      ∑ i : Fin n, hM.eigenvalues i *
        Complex.normSq (((hM.eigenvectorUnitary : Mat n)ᴴ *ᵥ v) i)
```

This is a finite spectral expansion; unlike a trace congruence identity, it
is valid for every Hermitian M and every vector. Root should review these
new proposed headers before their bodies are implemented.

## Bounded pinned API inspection

At Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, the inspected files provide:

- `Analysis/Matrix/Spectrum.lean`: `Matrix.IsHermitian.spectral_theorem`,
  `conjStarAlgAut_star_eigenvectorUnitary`, and the eigenvector-unitary inverse
  identities. No general negative-inertia theorem was found there.
- `LinearAlgebra/Matrix/Hermitian.lean`:
  `Matrix.isHermitian_conjTranspose_mul_mul` proves N Hermitian even for
  singular S; `Matrix.IsHermitian.inv` is available.
- `LinearAlgebra/Matrix/ConjTranspose.lean`: `Matrix.star_mulVec`, together
  with dotProduct/mulVec associativity and diagonal identities, supplies the
  quadratic covariance calculation.
- `LinearAlgebra/Dimension/StrongRankCondition.lean`:
  `LinearMap.finrank_le_finrank_of_injective`.
- `LinearAlgebra/Dimension/Constructions.lean`: finite function-space
  finrank formulas.
- `LinearAlgebra/QuadraticForm/Signature.lean`: real signature invariance
  exists, but that route requires an additional factor-two realification
  bridge. The direct complex dimension proof above avoids that obligation.

This is a bounded search, not an exhaustive claim that no other library
formulation exists. No Lean/compiler or Comparator was run by this author.
The source development still has no complete C11 proof or target-count change.
