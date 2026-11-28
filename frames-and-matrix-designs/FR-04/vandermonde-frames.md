# Exponential deterioration for Vandermonde frames

Use $`L(A)`$ and $`\omega(A)`$ from [FR-04](README.md). Let
$`d=n-1`$, and let the $`2n-1`$ rows of $`A`$ have the form

```math
a_i^{\mathsf T}
=s_i(w_j u_i^{d-j}v_i^{j})_{j=0}^{d},
\qquad s_i\ne0.
```

Here $`(u_i,v_i)`$ are nonzero pairs with distinct corresponding points
in the real projective line. The ordinary row-scaled Vandermonde
matrix is the case $`u_i=1`$ and $`w_j=1`$. The two choices of column
weights give

| Weights | Bound on $`\omega(A)/L(A)`$ |
| --- | --- |
| $`w_j=1`$ | $`\sqrt n/\sqrt{\binom{2n-2}{n-1}}`$ |
| $`w_j=\sqrt{\binom d j}`$ | $`\sqrt n\,2^{-(n-1)/2}`$ |

Both are bounded by $`C\beta^n`$ with absolute $`C>0`$ and
$`0<\beta<1`$. These matrices are full spark because a nonzero
homogeneous binary form of degree $`d`$ vanishes at no more than $`d`$
distinct projective points.

## Proof

At least $`n`$ indices satisfy $`u_iv_i\ge0`$, or at least $`n`$
satisfy $`u_iv_i\le0`$. Take an $`n`$-element subset $`T`$ of one of
these groups and choose $`\varepsilon\in\{1,-1\}`$ such that
$`\varepsilon u_iv_i\ge0`$ for $`i\in T`$. The coefficient vector
$`c_j=\binom d j(-\varepsilon)^j/w_j`$ satisfies
$`(A c)_i=s_i(u_i-\varepsilon v_i)^d`$.

For ordinary monomial weights, $`|u_i-\varepsilon v_i|\le
\max(|u_i|,|v_i|)`$. The norm of the $`i`$th row is at least
$`|s_i|\max(|u_i|,|v_i|)^d`$, by its two endpoint entries.
Thus $`|(Ac)_i|\le L(A)`$ on $`T`$. Also
$`\sum_{j=0}^d\binom d j^2=\binom{2d}{d}`$, so testing the unit vector
$`c/\|c\|_2`$ proves the first bound. The central binomial coefficient
is at least $`4^d/(2d+1)`$, which gives exponential decay.

For binomial-square-root weights, the binomial theorem gives
$`\|a_i\|_2=|s_i|(u_i^2+v_i^2)^{d/2}`$ and $`\|c\|_2=2^{d/2}`$.
On $`T`$, $`(u_i-\varepsilon v_i)^2\le u_i^2+v_i^2`$, so again
$`|(Ac)_i|\le L(A)`$. Testing $`c/\|c\|_2`$ proves the second bound.

Finally, for any invertible matrix $`W`$ of order $`n`$,

```math
\frac{\omega(AW)}{L(AW)}
\le \|W\|_2\|W^{-1}\|_2\frac{\omega(A)}{L(A)}.
```

For the numerator, choose a minimizing row set and test its minimizing
unit vector pulled back through $`W^{-1}`$ and normalized. For the
denominator, $`L(A)\le L(AW)\|W^{-1}\|_2`$. Multiplication by a factor
$`e^{o(n)}`$ preserves exponential decay along a family.
