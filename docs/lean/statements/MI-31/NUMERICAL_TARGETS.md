# MI-31 exact mathematical and numerical target

This pre-implementation specification is for the complete canonical
`matrix-inequalities-and-norms/MI-31/README.md` at published base
`0e916df335209819b5bf9bb8ed8f65ea978c049d`. Its bytes are retained
separately as `ORIGINAL.md`. This file states no proof of the Gaussian
operator-norm inequality.

For every positive pair of natural dimensions `m,n`, every real matrix
`A : Fin m → Fin n → ℝ`, every real input exponent `1 ≤ p ≤ 2`, and every
output exponent `q` in the **extended** range `2 ≤ q ≤ ∞`, draw one
independent standard real Gaussian `g_ij ~ N(0,1)` for every entry `(i,j)`.
The joint law is the finite product of these Gaussian measures. Set
`G_A(i,j)=A(i,j)g(i,j)`. There is no symmetry, sign, boundedness, rank,
normalization or square-matrix restriction on `A`.

The ordinary finite-dimensional vector norms are

```text
‖x‖_r = (∑ |x_i|^r)^(1/r)          for finite 1 ≤ r < ∞,
‖x‖_∞ = max_i |x_i|.
```

The induced norm is the genuine supremum
`‖B‖_(p→q) = sup {‖Bx‖_q : ‖x‖_p ≤ 1}` over every real input vector.
The conjugate exponent is `p* = p/(p−1)` for `p>1` and `p*=∞` for `p=1`.
Thus both `p*=∞` and `q=∞` endpoint vector norms must be the maximum norm.

For a positive integer `k`, let `L(k)=max(1,ln k)` with the natural log.
Define exactly

```text
D₁ = max_i ‖(A(i,j))_j‖_(p*),
D₂ = max_j ‖(A(i,j))_i‖_q,
Z  = E_g max_(i,j) |A(i,j)g(i,j)|.
```

The finite coordinate maxima occur **inside** the expectation only for
`Z`; `D₁,D₂` are deterministic. The exponent caps use the conventions
`min(∞,L(k))=L(k)`, so `sqrt(min(p*,L(n)))` and
`sqrt(min(q,L(m)))` remain finite at both infinity endpoints. The exact
comparison is the **upper bound only**

```text
∃ C : ℝ, 0 < C ∧
  ∀ m,n≥1, ∀ 1≤p≤2, ∀ 2≤q≤∞, ∀ A∈ℝ^(m×n),
    E_g ‖G_A‖_(p→q) ≤
      C [sqrt(min(p*,L(n))) D₁
         + sqrt(min(q,L(m))) D₂ + Z].
```

The single `C` is chosen before **all** dimensions, exponents and variance
profiles. `p` and `q` may vary with dimension; constants depending on
the exponents would weaken the target. There is no matching lower-bound
claim with these terms. The endpoint cases `p=1`, `p=2`, `q=2`, `q=∞`,
and dimensions `m=1` or `n=1` are included.

The canonical resolution cites an informal audit of a candidate proof and
an entropy-cardinality convention correction. That proof-status caveat is
retained in `ORIGINAL.md`; it does not alter the displayed target. No
floating-point calculation, numerical Gaussian sampling, or optimization
enumeration is needed merely to state this symbolic inequality. A Lean
boundary must use concrete finite-dimensional norms, Gaussian product law,
and expectations, not a free `OperatorNorm` or `GaussianExpectation`
parameter whose meaning is supplied as an assumption.
