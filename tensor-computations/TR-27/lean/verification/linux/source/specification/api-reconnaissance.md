# TR-27 API reconnaissance and complete-target representation

Date: 2026-09-22. Reviewer: `/root/canonical_inventory`, a Codex AI agent independent of the coordinating implementer. This is a bounded source/API inspection. No Lean proofs were implemented, no new declaration was type-checked, and [TR-27-TARGETS.md](TR-27-TARGETS.md) was not edited. The mathematical target and original attribution remain as recorded there.

## Source inspected and provenance limit

Inspected `/private/tmp/mf21-mathlib-source-20260920/Mathlib` as requested. Its `lean-toolchain` is `leanprover/lean4:v4.33.1`. The repository's current MF-21 and campaign MF-03 manifests identify Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. This extracted source directory has no `.git`, so a `git rev-parse HEAD` check cannot independently authenticate its revision. The API descriptions below refer to the actual local bytes; selected hashes are recorded at the end. Compilation against the final lockfile remains necessary.

## Recommendation

Use Mathlib's existing `Projectivization` for projective points and spans, and a homogeneous prime ideal in a finite complex polynomial ring for the variety and its Zariski closure. Use the actual `TensorProduct` for the final statement. Prove explicit equivalences to the affine-cone rank predicates used in the algebraic proof.

This hybrid presentation preserves the complete original target while avoiding a premature dependency on a point-level equivalence between `Projectivization` and scheme-level `Proj`. Such an equivalence was not located in this source search. The most promising way to prove the indispensable closed-image equality is **an explicit integral ring map plus lying over and the Nullstellensatz**; a small exact identity described below makes this route concrete.

## Projective points, representative independence and spans

| Module | Declarations inspected | Relevance and restriction |
|---|---|---|
| `Mathlib.LinearAlgebra.Projectivization.Basic` | `Projectivization`, `Projectivization.mk`, `.rep`, `.rep_nonzero`, `.mk_rep`, `.mk_eq_mk_iff`, `.mk_eq_mk_iff'`, `.lift`, `.lift_mk`, `.ind` | Existing projective points are nonzero vectors modulo nonzero scalar multiplication. `mk_eq_mk_iff'` gives equality by a scalar relation; nonzero representatives force that scalar to be nonzero. |
| Same module | `Projectivization.submodule`, `.submodule_mk`, `.submodule_eq`, `.equivSubmodule`, `.finrank_submodule` | A projective point corresponds to its actual one-dimensional linear subspace. |
| Same module, section `Map` | `Projectivization.map`, `.map_mk`, `.map_injective` | **Requires an injective semilinear map on the whole ambient space.** It cannot directly project the rank-twelve map `P : ℂ¹³ → ℂ¹²`. Define the map on the curve/nonvanishing domain, or descend its homogeneous parametrization with `lift`. |
| `Mathlib.LinearAlgebra.Projectivization.Independence` | `Projectivization.Independent`, `.independent_iff`, `.independent_iff_iSupIndep`, `.independent_pair_iff_ne` | Converts independence of projective points to independence of the chosen representatives. This is the right statement for the uniform eight-point obligation. |
| `Mathlib.LinearAlgebra.Projectivization.Subspace` | `Projectivization.Subspace.span`, `.subset_span`, `.span_le_subspace_iff`, `.mem_span`, `.submodule`, `.mem_submodule_iff` | Provides projective spans and the order isomorphism from projective subspaces to linear submodules. |
| Same module, namespace `Submodule` | `Submodule.projectivization`, `.mk_mem_projectivization_iff`, `.mem_projectivization_iff_submodule_le` | Direct representative membership bridge for finite projective spans and nondegeneracy. |

The `Projectivization` modules inspected do not install a Zariski topology. A repository-local zero-locus/closure definition on these projective points therefore needs a precise mathematical definition and equivalence lemmas, not an assumed ambient `closure` operation. Global searches for `Projectivization` in `Mathlib/AlgebraicGeometry` and `Mathlib/RingTheory` did not find a `Projectivization`/`Proj` bridge. This is a bounded negative search, not a claim that every equivalent API name has been excluded.

## Polynomial zero loci, homogeneity and reducedness

| Module | Declarations inspected | Use |
|---|---|---|
| `Mathlib.RingTheory.Nullstellensatz` | `MvPolynomial.zeroLocus`, `.mem_zeroLocus_iff`, `.vanishingIdeal`, `.mem_vanishingIdeal_iff` | Affine complex zero loci and all-polynomial vanishing ideals; `zeroLocus` uses `aeval`. |
| Same module | `.zeroLocus_vanishingIdeal_le`, `.zeroLocus_vanishingIdeal_galoisConnection`, `.le_zeroLocus_iff_le_vanishingIdeal` | Extensivity, closure construction and the inclusion/ideal reversal. Despite its name, `zeroLocus_vanishingIdeal_le` has type `V ≤ zeroLocus K (vanishingIdeal k V)`. |
| Same module | `.eq_vanishingIdeal_singleton_of_isMaximal`, `.isMaximal_iff_eq_vanishingIdeal_singleton` | A maximal ideal in a finite-variable polynomial ring is evaluation at an algebraically closed-field point. This supplies the parameter point after lying over. |
| Same module | `.vanishingIdeal_zeroLocus_eq_radical`, `MvPolynomial.IsPrime.vanishingIdeal_zeroLocus` | Strong Nullstellensatz and the prime-ideal special case. These give faithful algebraic-set/ideal correspondence. |
| `Mathlib.RingTheory.MvPolynomial.Homogeneous` | `MvPolynomial.IsHomogeneous`, `.homogeneousSubmodule`, `.IsHomogeneous.aeval`, `.homogeneousComponent`, `.homogeneousComponent_isHomogeneous`, `.sum_homogeneousComponent` | The coordinate substitution sends degree `d` to degree `12d`; distinct degrees remain distinct. These APIs support proving its kernel homogeneous. |
| `Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal` | `Ideal.IsHomogeneous`, `.IsHomogeneous.mem_iff`, `HomogeneousIdeal`, `.toIdeal`, `.isHomogeneous`, `Ideal.homogeneous_span` | Use the usual total-degree grading `MvPolynomial.homogeneousSubmodule J ℂ`. Homogeneity means closed under all homogeneous projections; it is not merely a label. |
| `Mathlib.RingTheory.Ideal.Maps` | `RingHom.ker_isPrime` | The kernel of a ring homomorphism into the domain `ℂ[s,t]` is prime. |
| `Mathlib.RingTheory.Ideal.Quotient.Basic` | `Ideal.Quotient.isDomain`, `.isDomain_iff_prime` | A prime ideal gives a domain coordinate ring. |
| `Mathlib.RingTheory.Ideal.Quotient.Nilpotent` | `Ideal.isRadical_iff_quotient_reduced` | Explicit reduced-coordinate-ring semantics. |
| `Mathlib.FieldTheory.IsAlgClosed.Basic` | `IsAlgClosed.exists_pow_nat_eq` | Every complex scalar has a twelfth root. This shows the degree-twelve homogeneous image already includes every scalar multiple of each projective representative. |
| `Mathlib.Algebra.Polynomial.Roots` | `Polynomial.eq_zero_of_infinite_isRoot`, `.eq_of_infinite_eval_eq`, `.zero_of_eval_zero` | The polynomial degeneration proves the border bound with no analytic limit or interval arithmetic. |

`PrimeSpectrum.isIrreducible_zeroLocus_iff` and `PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime` exist in `Mathlib.RingTheory.Spectrum.Prime.Topology`, but their sets consist of **prime ideals**. They do not directly prove `IsIrreducible` for a set of complex coordinate points. The point-level topology/Nullstellensatz bridge must be proved, or irreducibility should be encoded through the homogeneous prime ideal with a reviewed equivalence to the classical variety convention.

## A concrete closed-image route using integrality

Keep precisely the homogeneous coordinates of the target specification. In `S = ℂ[s,t]`, write

```math
H_j=5s^{12-j}t^j-S_js^{11}t,
\quad j\in J=\{0,2,\ldots,12\},
\quad S_j=1+2^j+3^j.
```

Let `R = ℂ[X_j : j∈J]`, let `φ : R →ₐ[ℂ] S` substitute `H_j` for `X_j`, and put `I = ker φ`. The following small identity was derived during this API assessment; it is a proposed exact algebraic bridge, not an implemented Lean theorem:

```math
a=s^{12},\qquad b=s^{11}t,
\qquad
85a^2+(8H_0+9H_2)a-5H_0^2=0.
```

Indeed `H_0=5a−3b` and `aH_2=5b²−14ab`; eliminating `b` yields the displayed identity. Therefore `a` is integral over `R` through `φ`, using the monic quadratic obtained by dividing by `85`. Moreover

```math
b=(5a-H_0)/3,
\qquad
t^{12}=(H_{12}+535538b)/5.
```

Integral elements form a subring, so `b` and `t^12` are integral. From integrality of `s^12` and `t^12`, both `s` and `t` are integral. Every polynomial in them is then integral, hence `φ` is an integral ring map.

This uses only the original `H_0,H_2,H_12` coordinates, and imposes no affine-chart denominator or nonzero-coordinate assumption on an output point. In particular it covers zero and the infinity direction. The general base-point-free/proper-morphism theorem is unnecessary for this particular closed-image argument if the integral route is completed.

Precise existing support:

- `RingHom.IsIntegralElem`, `RingHom.IsIntegral`, and `IsIntegral` in `Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs` are defined by monic polynomial witnesses.
- `IsIntegral.of_pow` in `Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic` takes `0 < n` and integrality of `x^n`, concluding integrality of `x`. The same module has `isIntegral_algebraMap`.
- `IsIntegral.add`, `.sub`, `.mul`, `.neg` and their `RingHom.IsIntegralElem` forms are in `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`.
- `MvPolynomial.induction_on` in `Mathlib.Algebra.MvPolynomial.Basic` can lift integrality of coefficients and variables to every element of `S`.
- `Ideal.exists_ideal_over_maximal_of_isIntegral` in `Mathlib.RingTheory.Ideal.GoingUp` has the useful noninjective form: for a maximal ideal `M` of `R`, given `ker(algebraMap R S) ≤ M`, it provides a maximal ideal `N` of `S` whose comap is `M`. There is no need to first prove `φ` injective, which would be false.
- `MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal` then identifies `N` with evaluation at some `(s,t)∈ℂ²`.

For any `w ∈ zeroLocus ℂ I`, its evaluation ideal `M_w` is maximal and contains `I`. Apply the two preceding APIs. Evaluate `X_j−w_j` in the resulting equality of comaps to obtain `H_j(s,t)=w_j` for every `j`. This proves

```math
\operatorname{range}(H)=V(I).
```

The reverse inclusion direction from the range into the zero locus is immediate from substitution, but both directions must be exported or otherwise inspectable. This equality discharges the point-set part of the closed-image requirement without assuming it.

Remaining work in this route includes setting up the induced `R`-algebra on `S` without conflicting with its ordinary `ℂ`-algebra, checking the exact monic quadratic under `eval₂`, and proving the kernel homogeneous. All are actual proof obligations. The identity has been algebraically checked in this assessment but not mechanically certified. No interval calculation is needed.

## Actual tensor products and the support lower bound

| Module | Declarations inspected | Use |
|---|---|---|
| `Mathlib.LinearAlgebra.Basis.VectorSpace` | `Module.Basis.extend`, `.extend_apply_self`, `.sumExtend` | Extend each finite independent representative family to an ambient basis; its coordinate functionals are then available. |
| `Mathlib.LinearAlgebra.Dual.Lemmas` | `Module.Projective.exists_dual_eq_one` | For nonzero `v`, produces a linear functional with value one on `v`; vector spaces have the required projective-module instance. |
| `Mathlib.LinearAlgebra.TensorProduct.Map` | `TensorProduct.map`, `.map_tmul` | Contract one factor or transport tensors under linear equivalences. |
| `Mathlib.LinearAlgebra.TensorProduct.Basis` | `Module.Basis.tensorProduct`, `.tensorProduct_apply`, `.tensorProduct_repr_tmul_apply` | The exact product-basis coordinate formula. This supplies the support Cartesian product used to rule out eight summands. |
| Same module | `TensorProduct.equivFinsuppOfBasisRight`, `.equivFinsuppOfBasisRight_apply_tmul_apply`, `.equivFinsuppOfBasisLeft` | Alternative direct coordinate/contraction views. |
| `Mathlib.LinearAlgebra.TensorProduct.Pi` | `TensorProduct.piScalarRight`, `.piScalarRightHom_tmul`, `.piScalarRight_apply` | Canonical equivalence `(J→ℂ) ⊗[ℂ] (J→ℂ) ≃ₗ[ℂ] (J→(J→ℂ))`. On `x⊗y` it returns `j↦ y_j • x`; a transpose/reindex puts this in the desired `x_i y_j` order. |

The `TensorProduct.toMatrix_*` results in `Mathlib.LinearAlgebra.TensorProduct.Matrix` describe matrices **of tensor-product linear maps**. They are not themselves the desired vector-tensor-to-outer-product equivalence. `piScalarRight` or the product basis is the appropriate starting point.

No general projective Segre-map declaration was located by searches for `Segre` in the inspected algebraic-geometry/ring-theory sources. It is straightforward to define the point map using representatives only after proving: nonzero factors give a nonzero tensor, and changing either representative by a unit changes the tensor by the product unit. The final theorem must retain this actual point map or its explicit proved equivalent cone semantics.

## Scheme-level alternative and why it costs more

`Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology` contains `ProjectiveSpectrum`, `.zeroLocus`, `.vanishingIdeal`, `.zariskiTopology`, `.isClosed_iff_zeroLocus` and `.zeroLocus_vanishingIdeal_eq_closure`. These are homogeneous **prime spectrum** points, including nonclosed generic points, rather than the vector lines of `Projectivization`.

`Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor` contains `ProjectiveSpectrum.comap` and `AlgebraicGeometry.Proj.map`. The inspected construction requires a graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ` and an irrelevant-ideal inclusion `ℬ₊ ≤ 𝒜₊.map f`. The degree-twelve parametrization is not directly a degree-preserving map between the ordinary degree-one gradings; regrading/Veronese work or a different construction would be necessary.

`Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper` supplies `IsProper (Proj.toSpecZero 𝒜)` when the graded ring is finite type over degree zero. `Scheme.Hom.isClosedMap` in `Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed` yields a closed underlying map from a universally closed morphism. These powerful APIs do not by themselves construct this concrete parametrization, identify its closed complex points, or identify its point image with the vectors used in the rank proof.

The scheme route is mathematically sound but has more integration work than the explicit integral-image argument above. It should not be selected merely because a theorem named `IsProper` is present.

## Feasible complete theorem boundary and required equivalences

A credible final boundary can use `V = J → ℂ`, a homogeneous prime ideal `I` in `MvPolynomial J ℂ`, its affine zero locus `C`, and its subset `X` of `Projectivization ℂ V`. The principal exported result can say that this `X` is an irreducible reduced nondegenerate complex projective variety and that the displayed projective point has rank three, border rank at most two and Segre-square rank nine; a subsequent declaration negates the full canonical implication.

If “projective variety” is represented by a homogeneous prime ideal instead of a new scheme object, statement review must inspect a real classical-coordinate definition: nonempty projective zero set, homogeneous equations, reduced coordinate ring, prime vanishing ideal, and full projective span. These must not be packaged as an arbitrary predicate carrying the desired answer as data.

The following new bridges are still needed; none was found as a ready-made complete theorem during this inspection:

1. **Finite span/rank:** projective span membership is equivalent to an unrestricted complex linear combination of representatives. Padding with zero terms preserves the at-most predicate. Nondegeneracy supplies finite decompositions, so minimum-rank definitions cannot default on an empty set.
2. **Cone/projective zero loci:** for a homogeneous ideal, vanishing is independent of the nonzero representative; all projective points are exactly the nonzero affine-cone points modulo scaling.
3. **Cone/projective Zariski closure:** the projectivization of the all-polynomial affine closure of a scaling-invariant rank cone equals the common zero set of all homogeneous equations vanishing on its projective rank locus. Homogeneous decomposition or scalar-parameter polynomial uniqueness supplies the proof.
4. **Irreducibility at classical points:** derive the irreducible-zero-set convention from the prime homogeneous ideal and Nullstellensatz, or prove the equivalent closed-set union criterion directly. The `PrimeSpectrum` theorem cannot be applied to classical coordinate points without this bridge.
5. **Actual image:** prove `range(H)=zeroLocus(ker φ)` using the integral map above; then prove that nonzero homogeneous image points are exactly the finite-parameter and infinity representatives. `IsAlgClosed.exists_pow_nat_eq` handles arbitrary scalar multiples.
6. **Segre/rank:** define the Segre point map with actual tensor products and prove the cone decomposition equivalence. No symmetric-factor constraint or merged-mode convention may enter.

These bridges do not weaken the target. They make its exact semantics available to Lean in an area where the convenient point APIs and scheme APIs are currently separate. The recommended next TR-27 milestone is to settle and independently review these definitions and equivalences before implementing the rank proof.

## Byte binding for selected inspected modules

All paths below are relative to the inspected extracted Mathlib root; hashes are SHA256.

| File | SHA256 |
|---|---|
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `Mathlib/LinearAlgebra/Projectivization/Basic.lean` | `1d299efb79860b3eea0ebf94ef3b3a1d32df7d6593c13b3f9835b6584e9340b2` |
| `Mathlib/LinearAlgebra/Projectivization/Subspace.lean` | `d86fcfda1d39221fa6e54364f5415c55d1d8d8c4391d56d01974f3086f63e4fd` |
| `Mathlib/RingTheory/Nullstellensatz.lean` | `4cff1e3d1983296280326087593b18b6a055088727c9b5e768291a0459f24ee1` |
| `Mathlib/RingTheory/Ideal/GoingUp.lean` | `513d648edbc834a1f9bab5cba6062f7c6a3cf5e73dda3eb9007aba8e1bd6517f` |
| `Mathlib/RingTheory/IntegralClosure/IsIntegral/Basic.lean` | `bb76f4dbd3f92ef704e9146fbd8b737e417b662ba39e9b2d6732a96684611b03` |
| `Mathlib/LinearAlgebra/TensorProduct/Basis.lean` | `ce068c65f80addfbf4d9d9e2849249f0811ccf5d04119beca1b111455401edc5` |
| `Mathlib/LinearAlgebra/TensorProduct/Pi.lean` | `0dbf8b30e9a3f480663561b654ebccf106373131e13a7d9b89100c9c6e50bd95` |
