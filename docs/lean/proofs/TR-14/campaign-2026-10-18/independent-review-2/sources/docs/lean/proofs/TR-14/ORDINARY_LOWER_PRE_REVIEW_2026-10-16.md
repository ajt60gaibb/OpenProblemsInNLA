# TR-14 ordinary-rank lower bound: pre-proof contract

**Phase:** exact mathematical and numerical statement, before Lean implementation.
**Source:** the unchanged `tensor-computations/TR-14/solution.tex`, Section 4
(`lem:transform`, `lem:context`, `cor:trivial`) and Section 5 (`prop:lower`),
read with the canonical `tensor-computations/TR-14/README.md` and the live and
frozen `NLA.Statements.TR14.Target`. This contract is not a Lean proof.

## Public theorem required by the full target

Let `m ≥ 3`, `n ≥ 2`, `q = n − 1`, and `D = m q`. Let `h` be any nonzero complex
moment vector of length `D + 1`. Let `r₀` be the least degree of a nonzero
homogeneous binary apolar polynomial for `h`, and choose **any** nonzero
degree-`r₀` apolar polynomial `G`. Let `s` be the number of its distinct
projective roots, counted without multiplicity. For **every** natural `R`,

> `OrdinaryWidth (Hankel h) R` implies
> `min (D − r₀ + 2) ((m − 1) r₀ − (m − 2) s) ≤ R`.

Lean may state this with natural or integer arithmetic, provided the casts and
subtractions are proved equivalent on the source domain. The endpoints
`r₀ = 1`, `r₀ > n`, repeated roots, mixed multiplicities, and the balanced
case `D = 2 r₀ − 2` remain included. No genericity, squarefreeness, finite-root
only count, Vandermonde restriction, or symmetric ordinary summands may be
assumed. The zero tensor is excluded only from this *intermediate* theorem;
the final all-width target handles it separately. If a normalized affine
chart is used internally, transport the result back to the original `h` and
count all projective roots of `G`, including infinity. An equivalent chart
root count is acceptable only with a proved projective-root bijection.

The source states the minimum-rank version `Rk(H) ≥ min{…}`. The all-`R`
implication above follows from it by minimum existence and zero padding and
is the interface needed for the live all-width `Target`; it has the same
mathematical content. Its two candidate bounds must remain **both** present.
For example, the source's `m=5,n=3,r₀=4,s=2` double-point case gives local
bound `10` and binary bound `8`, so replacing the minimum by the local bound
would be false.

## Required source-bound proof obligations

1. **Moment algebra.** Construct the Frobenius algebra `A=ℂ[t]/(g)` from a
   least apolar polynomial and transport by `GL₂` when needed. Its dimension
   is `r₀`; all-but-one products of degree-at-most-`q` mode factors span `A`.
   The CRT local factors are `ℂ[z_a]/(z_a^ℓ_a)`, with `∑ℓ_a=r₀` and `s`
   factors. For every union of factors of dimension `r_j`, the mode-image
   dimension is `min(n,r_j)`.
2. **Transformation and contextual inequality.** In any finite-dimensional
   commutative complex algebra `B`, for unit-containing `U,V` and each unit
   `a∈U`, produce `K_a,T_a` with `aV⊆T_a⊆UV`, `K_a T_a=T_a`, and
   `dim T_a+dim K_a≥dim U+dim V`. In `B=A×ℂ^R`, impose an annihilating
   functional whose restriction to `A` is Frobenius, `1∈U_i`, and
   `π_A(∏_{k≠i} U_k)=A` for **every** `i`. These hypotheses must imply each
   auxiliary `K_a` is reduced, the stabilizer `Stab(W)` is reduced, and
   `dim W_j≥dim W_{j−1}+dim U_j−dim Stab(W_j)` for `j≥2`. The finiteness of
   reduced subalgebras and common-`K` Vandermonde-basis argument must be
   justified; an unrestricted Kneser theorem over nonreduced algebras is not
   a substitute. With `Stab(W)=ℂ1`, deduce
   `dim W≥∑_i dim U_i−(m−1)`.
3. **Arbitrary ordinary decomposition.** Start with a minimum ordinary
   decomposition of `Hankel h` with `R` summands and arbitrary, potentially
   mode-dependent nonzero factors `β_{b,i}`. Prove its decomposable tensors
   linearly independent. Graph each mode factor together with its image in
   `A`, select unit graph elements, and normalize to subspaces containing
   `1`. Prove Frobenius annihilation, every all-but-one projection condition,
   and `π_{ℂ^R}(W)=ℂ^R`. The normalized functional must have nonzero
   coefficient on each `ℂ` coordinate.
4. **Primitive blocks.** Partition the reduced final stabilizer into
   primitive-idempotent blocks `B_j=A_j×ℂ^{R_j}`. Exclude blocks with
   `A_j=0`; every block has `r_j≥1`, `s_j≥1`, and a trivial block
   stabilizer. Retain `∑r_j=r₀`, `∑R_j=R`, `t≤s`, and
   `dim U_i^(j)≥min(n,r_j)`. The exact block inequality is
   `R_j≥m·min(n,r_j)−r_j−m+2`.
5. **Numerical finish.** If some `r_j≥n`, infer
   `R≥D−r_j+2≥D−r₀+2`. If all `r_j<n`, sum block bounds to get
   `R≥(m−1)r₀−(m−2)t≥(m−1)r₀−(m−2)s`. These inclusive alternatives
   establish the stated minimum. Then pass from minimum `R` to any larger
   ordinary width by a proved width/minimum relation.

## Boundary and review gate

`NLA.Statements.TR14.Target` quantifies over all `m,n,h,R` and equates
actual finite-coordinate `OrdinaryWidth` and `SymmetricWidth`; this lower
theorem supplies one nonzero direction only. It does not itself establish
the binary or local symmetric upper bounds, the zero case, or the final
all-width equivalence. A second agent must independently compare this
contract with the source and live/frozen target before implementing its
Lean theorem. A subsequent final review must inspect the exact implemented
signature and proof source before any Lean-verified status or PR.
