# TR-20 exact mathematical and numerical target

Status: pre-implementation specification. The complete canonical page at `tensor-computations/TR-20/README.md` is preserved byte for byte in `ORIGINAL.md`. The published base is `0e916df335209819b5bf9bb8ed8f65ea978c049d`. This describes a Lean **statement**, not a proof of the discriminant formulas.

## Rank-one Rayleigh–Ritz geometry

For positive integers `m,n` with `m,n ≥ 2`, put `N=mn` and use ordinary entry coordinates indexed by pairs `(i,j)`. A rank-one state is the projective class of the actual vector `ψ = vec(a bᵀ) ∈ ℂ^N` for nonzero `a∈ℂ^m` and `b∈ℂ^n`. The resulting smooth Segre variety is `V_(m,n) ⊂ ℙ^(N−1)`, equivalently `ℙ^(m−1) × ℙ^(n−1)` under the Segre embedding. Quotienting either factor by nonzero complex scale must not change the state. It is **not** the full projective matrix space or a higher tensor-rank variety.

The parameter space is the projectivization of the full complex vector space of **symmetric** `N×N` matrices `H`, with `Hᵀ=H` and `H≠0`. The parameter is `[H]` modulo nonzero complex scalar. Define

```text
Q(a,b) = ψᵀψ = (aᵀa)(bᵀb),
P_H(a,b) = ψᵀHψ,
R_H([ψ]) = P_H(a,b)/Q(a,b)     when Q(a,b) ≠ 0.
```

Every transpose is the ordinary **complex bilinear** transpose, never conjugate transpose or Hermitian adjoint. The numerator is bihomogeneous of bidegree `(2,2)`, as is `Q`, so the ratio is independent of projective representatives. The nonisotropic open set `U ⊂ V_(m,n)` is exactly `Q≠0`; points on either quadric boundary `aᵀa=0` or `bᵀb=0` are excluded from the critical-point incidence.

At `[ψ]∈U`, criticality means the differential of the actual rational function `R_H` restricted to the Segre variety vanishes on its full `m+n−2` dimensional tangent space. Degeneracy means the Hessian of that restricted function at this critical point is singular on the same tangent space. One may define these through any local product of projective affine charts: the vanishing differential and Hessian singularity are chart-independent at a critical point. A condition on the ambient Hessian in `ℂ^N`, a Hermitian Hessian, or only one factor's tangent directions would change the target.

## Nonisotropic projective discriminant and its degree

Let `S_(m,n)` consist of projective classes `[H]` of nonzero complex symmetric matrices for which **there exists** a nonisotropic Segre point that is critical and degenerate as above. Define `Δ^ni_(m,n)` as the **Zariski closure** of this locus in the complete projective symmetric-matrix parameter space `ℙ(Sym² ℂ^N)`. This closure may contain boundary or limit parameters, but an isotropic point by itself must not be used to generate the incidence. In particular, a discriminant built by allowing `Q=0` as a critical point is a different object.

The source asks for `Δ^ni_(2,n)` and `Δ^ni_(3,n)` to be hypersurfaces and for their **reduced projective degrees** to obey, for every integer `n≥2`,

```text
deg Δ^ni_(2,n) = 24 * binomial(n+1, 3),
deg Δ^ni_(3,n) = 24 * n^2 * binomial(n, 2).
```

These are exact natural-number identities, with the ordinary combinatorial binomial coefficient, including `n=2`; there is no numerical tolerance or finite test range. Projective degree means the intersection count with a general projective line, equivalently the homogeneous degree of a reduced defining equation for a hypersurface. A scheme-theoretic ramification count with an unverified generic multiplicity is not a substitute. The two formulas and both hypersurface assertions form **one** conjecture. The resolution's stronger irreducibility claim and general coefficient formula may aid a proof, but are not additional obligations of the retained target.

For implementation, the Lean boundary must define the actual Segre/nonisotropic critical-degenerate incidence and its Zariski closure (or a proved equivalent concrete algebraic construction), then assert the hypersurface property and reduced degrees in the original symmetric-matrix parameter space. A free `DiscriminantDegree` oracle, direct assignment of the two answer values, an uninterpreted critical-point predicate, replacement by the space of all `(2,2)` sections without a proved degree-preserving pullback, or a statement only about the finite diagnostics would weaken or alter the target. The rank-one Segre, bilinear transpose, nonisotropic restriction, reduced degree, and all-dimensional quantifier are essential.
