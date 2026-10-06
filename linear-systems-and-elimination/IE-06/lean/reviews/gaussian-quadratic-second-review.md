# Second independent review of the Gaussian quadratic core and A4-min plan

Date: 2026-10-06. Reviewer: `/root/independent_math_review`, independently of
both the implementer and the coordinating reviewer. Reviewed module SHA-256:
`0a2ce297b2d3210bb0866579ea39972b2bdc089b3d341af6efc0f15777f8d137`.
Reviewed specification SHA-256:
`4efcc11bc3441d403d503e9a006079b6af87ef23f708f6ec1a10fc12080e657e`.

The scalar identity admits every parameter below one half, including negative
parameters. Multiplying by the Gaussian density leaves a Gaussian kernel with
positive coefficient `1/2 - s`; its exact integral is
`1 / sqrt(1 - 2s)`. Integrability is proved explicitly. Product factorization
uses the actual finite independent Gaussian law and requires only
`t * w_i < 1/2`; the empty-dimensional case follows from the empty product.

For `0 ≤ s ≤ 1/4`, the code combines `(1 - 2s)⁻¹ ≤ 1 + 4s` and
`1 - (1 - 2s)⁻¹ ≤ log(1 - 2s)` in the correct direction, giving the stated
MGF bound including its closed endpoint. The positive parameter `1/(4L)`
puts all `0 ≤ w_i ≤ L` in this range. Chernoff first controls the non-strict
tail, then the required strict exceedance by containment. The exponent
simplifies exactly to `-x` at threshold `2 sum w_i + 4Lx`. Probability
finiteness justifies the real/extended-real conversion.

**Approved as a scalar/product concentration core.** No hidden assumption,
unproved manuscript input, or mathematical defect was found. A matrix
Frobenius/operator concentration theorem still requires its separate spectral
and invariance bridge.

## Independent mathematical review of A4-min

The full-proof specification was read at SHA-256
`90c1d10687e32fa421285e52f8131e5e6261eeb7d8232475e8639faf86504387`.
Its filtration correction is right: first `t` completed pivots and `E_t`
depend on the first `t` columns, whereas the next pivot needs the next column.
The centered Section 4–5 contracts and their explicit domain guards have been
reviewed for correspondence, not as a complete independent audit of every
external analytic paper.

The proposed A4-min route is mathematically valid. A scalar subgaussian with
variance proxy one satisfies `E exp(Y²/4) ≤ sqrt 2` by introducing an independent
Gaussian auxiliary variable and using Tonelli. Normalize nonzero matrix
columns and apply finite Jensen with weights equal to their squared norms
divided by the squared Frobenius norm. The weights sum to one and the scalar
projections need not be independent. This yields
`E exp(‖XᵀM‖²/(4‖M‖F²)) ≤ sqrt 2`. Markov at
`(2 + 4x)‖M‖F²`, using `log 2 ≤ 1`, gives exactly the estimate needed in B1.
The zero-matrix case is an empty event.

Completing the square correctly derives the vector MGF from the symmetric
convex Gaussian shift inequality. That inequality remains a substantive
theorem to prove; no proof of it is supplied or assumed by this approval.

## Review of the specialized stopping-count proposal

For `λ ≥ 256`, `J = ceil(sqrt λ)`, and starting rank `d ≥ J`, the proposed
recursion `d_next = max(100d, ceil(d²/λ))` reaches `100λ` within `J` steps:
`100^J d ≥ 100J² ≥ 100λ`. After another `J` steps its value is at least
`λ 100^(2^J) ≥ exp λ`, since `J ≥ 4`, `2^J ≥ J² ≥ λ`, `log 100 ≥ 1`,
and `λ ≥ 1`. Thus the stopped sum has at most `2J` terms. Its reciprocal part
is bounded by `2λ/d` using geometric growth, so the sum is at most
`2J + 2λ/d ≤ 6 sqrt λ`. This is sufficient for the unchanged final target
at `r = J`; it is not the sharper arbitrary-r logarithmic source estimate.
