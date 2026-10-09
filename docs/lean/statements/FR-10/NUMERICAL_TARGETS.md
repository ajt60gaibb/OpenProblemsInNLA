# FR-10 exact mathematical and numerical target

Source: the complete original statement and resolution in
`frames-and-matrix-designs/FR-10/README.md` at the published base
`0e916df335209819b5bf9bb8ed8f65ea978c049d`. This is a statement
specification, not a proof of the Walsh restricted-isometry theorem.

For every integer `d ≥ 1`, set `G = (𝔽₂)^d` and `N = 2^d`. Index both rows
and columns of the normalized Walsh matrix by `G`, with
`H(a,b) = N^(-1/2) (-1)^(a·b)`. For every positive sample count `m`, a sample
is an **ordered** function `a : Fin m → G` drawn uniformly from all `N^m`
functions. Its coordinates are therefore independent uniform draws **with
replacement**. Repeated rows and sample counts above `N` remain admissible.

For `x : G → ℝ`, define `‖x‖₂² = ∑ b, x_b²` and
`‖Φ_a x‖₂² = (1/m) ∑ i, (∑ b, (-1)^(a_i·b) x_b)²`. The latter is exactly
the squared norm of the source matrix `Φ = √(N/m) H_(a₁,…,aₘ),:`; this
energy formula removes the square roots without changing the matrix or
target. The support is the finite set `{b : x_b ≠ 0}`.

`E(d,m,k,a)` holds when **the same sample** `a` satisfies, for **every**
real vector `x : G → ℝ` with support cardinality at most `k`, both weak
inequalities

```text
(1/2) ‖x‖₂² ≤ ‖Φ_a x‖₂² ≤ (3/2) ‖x‖₂².
```

`p(d,m,k)` is the exact rational probability
`|{a : Fin m → G : E(d,m,k,a)}| / N^m` under this finite uniform product
law. The success threshold is inclusive: `p(d,m,k) ≥ 9/10`, exactly.
`mStar(d,k)` is the **minimum positive** `m` meeting that threshold. The
formal target must ensure that the qualifying set is nonempty and that the
minimum has the stated property; it must not use the zero value of
`Nat.sInf ∅` as a substitute. No monotonicity of success in `m` is assumed.

The original question asks for universal multiplicative constants over the
entire sparsity range. The resolved target is

```text
∀ d ≥ 1, mStar(d,1) = 1;
∃ c C : ℝ, 0 < c ∧ 0 < C ∧
  ∀ d ≥ 1, ∀ k ∈ ℕ, 2 ≤ k ≤ 2^d →
    c k log(2k) log(2e·2^d/k) ≤ mStar(d,k) ≤
    C k log(2k) log(2e·2^d/k).
```

All logarithms are natural and `e = exp(1)`. The source's stronger explicit
lower coefficient `c = 1/2000` may be stated as an additional named
resolution target, provided the existential original target remains
present. The endpoint `d = 1`, `N = k = 2` and dense case `k = N` are
included. Colbrook's fixed-`k` numerical limits and dense endpoint
asymptotic are historical subsidiary results in the canonical page, not
substitutes for the full uniform FR-10 target. No approximation, floating
point computation, exhaustive sample enumeration, or numerical estimate is
needed to *state* the proposition.
