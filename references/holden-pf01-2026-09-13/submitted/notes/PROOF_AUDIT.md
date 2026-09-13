# Proof audit and scope

This is a self-audit, not independent mathematical review.

## Binary-pattern counting

The counting theorem uses real symmetric matrices and real nonzero vectors for the attained patterns. Complex projective geometry is used only for an upper bound. The chart `p(u)=u^T u != 0` contains every real nonzero vector. The 64-point Bezout bound applies to isolated roots. A separate fiber lemma allows at most one extra binary pattern from a positive-dimensional component when the trace-zero linear kernel has dimension at most two. When that kernel has dimension at most one, there is no extra pattern.

The independent matrices `Q_i` are linear combinations of PSD factors; the `Q_i` themselves are not asserted to be PSD or measurement effects. The normalization is legitimate because a common kernel would force a factor span of dimension at most six, below rank eight or nine. The counting result does not exclude factors of ranks two or three.

## Projection-family theorem

The quadratic slice identity requires `2 <= r <= n-2`; the commutator subtraction additionally requires `r != 2`. The theorem is used with `r=3` or `r=4` only. The matrices `Z_i=V_i^2-V_i/r` commute with all coefficients and therefore with each other. Their simultaneous eigenspaces are invariant. On each block, the shifted coefficient span has scalar squares. The proof treats odd blocks and commuting blocks as well as the two possible noncommuting even block sizes.

For two noncommuting two-dimensional blocks, the scalar direction is shared because the shift is `I/(2r)` on each block for every coefficient. Counting it twice would give a weaker and incorrect dimension count for that case. The final maximum is five.

## Affine reduction and mixed ranks

The affine reduction is established for the side of span nine at order nine by the rank inequality `a+b <= 19`. It is not asserted for arbitrary order-seven or order-eight factors. The independent `X_i` are not assumed PSD. Their subset sums are PSD because they are the actual factors.

Normalizing the sum on eight indices is legitimate: a common kernel would confine eight independent coefficient matrices to a symmetric space of dimension at most six. Complementary rank-at-most-two sums of the identity must both be projections. The 252 covering constraints use six independent shifted coefficients and the span-five projection theorem.

## Exact quartic certificate

The 1008 derivative constraints are built directly from monomial derivatives at all 126 subset vectors. There are 495 homogeneous quartic monomials. The 90-column basis uses integer-scaled `z_i` and `h`. The exact integer kernel identity and two nonzero prime-field minors prove the rational ranks, which equal the real ranks.

The extra nine `h*x_i` directions are not optional. Their cubic factor and its gradient vanish on the slice, but its restricted Hessian is `3*diag(epsilon)`, not a scalar matrix. The argument excluding the 81-dimensional subspace cannot be extended by ignoring this term. This was an attempted extension in the current round; it is not a retraction of the prior manuscript's bounds.

## Determinant Hessian

The rank-three case is a negative sum of three squares on the tangent space. The rank-two case uses the determinant of a 2-by-2 kernel compression subject to orthogonality to a nonzero PSD matrix; its restricted determinant is nonpositive and has quadratic-form rank at most two. Rank one contributes no second-order term. No factor rank is assumed constant across subsets.

## What is not established

No mixed-rank size-four factorization has been ruled out at orders seven, eight, or nine. No smaller exact construction was found in this round. No matching unrestricted lower bound for the general graph construction is supplied. Failed local searches are not certificates.

The explicit functions `f=(1-x_1)(2-x_3-x_4)` and `g=x_1(2*x_3-1)` demonstrate that the listed nonnegativity, support, covering, and annihilator conditions alone do not produce a contradiction. They are not factors or determinant data.
