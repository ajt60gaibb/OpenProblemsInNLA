# RA-06 exact mathematical and numerical target

This is a **pre-implementation specification**, not a proof or an independent
review. `ORIGINAL.md` preserves `randomized-and-low-rank-approximation/RA-06/README.md`
byte for byte at published base `0e916df335209819b5bf9bb8ed8f65ea978c049d`.
The negative resolution is Theorem 5.1 of
`references/haidary-resolutions-2026-09-30/ra06-counterexample-revised.tex`.

## Exact ordinary-sensitivity sampler

Fix an **arbitrary real** exponent `p > 2`. The constants below may depend on
this fixed `p`, but on nothing else. For every positive pair of dimensions
`n,d` and every real matrix `A : Matrix (Fin n) (Fin d) ℝ` with **full column
rank**, write its rows as `a_iᵀ`. Full column rank means the linear map
`x ↦ A x` is injective; hence for every nonzero `x : Fin d → ℝ`,

```text
‖A x‖_p^p = ∑ i : Fin n, |∑ j : Fin d, A i j · x j|^p > 0.
```

For noninteger real `p`, these are exact nonnegative-base real powers, not
integer powers or approximations. Define each **ordinary** row sensitivity
and their sum by

```text
s_i(A,p) = sup_{x ≠ 0} |∑ j, A i j · x j|^p / ‖A x‖_p^p,
S(A,p)   = ∑ i : Fin n, s_i(A,p).
```

The supremum ranges over **all** nonzero real vectors, with no distribution,
normalization, augmented `ℓ₂` sensitivity, leverage-score replacement, or
supremum over a restricted test set. The ratio is well-defined by full rank
and lies in `[0,1]`, so the sensitivity is a finite real number.

For each tolerance `0 < ε < 1/2`, failure parameter `0 < δ < 1/2`, and
chosen scalar `α > 0`, set **exactly**

```text
q_i = min {1, 1/n + s_i(A,p)/α}.
```

The additive floor `1/n`, cap at `1`, and strict positivity `q_i > 0` are
part of the target. A sampled outcome is a Boolean retention vector
`ω : Fin n → Bool`. Its exact probability is the finite product
`∏_i (q_i if ω_i is retained else 1−q_i)`. Thus rows are independently
retained with the prescribed, possibly unequal probabilities; no fixed-size,
dependent, or arbitrary-weight sampling may replace this law. Each retained
row is multiplied by `q_i^(−1/p)`, and discarded rows contribute zero.
Equivalently, the sampled **norm power** is

```text
‖Ã_ω x‖_p^p = ∑_{i : ω_i retained} |∑ j, A i j · x j|^p / q_i.
```

This energy identity is exact because `q_i>0`; using it avoids computing
`p`th roots when stating the proposition. The expected number of retained
rows is exactly `∑_i q_i`, not a realized sample count.

The embedding event for one outcome `ω` is the conjunction of both **weak**
inequalities for **every** real `x : Fin d → ℝ` simultaneously:

```text
(1−ε) ‖A x‖_p^p ≤ ‖Ã_ω x‖_p^p ≤ (1+ε) ‖A x‖_p^p.
```

Its probability is the finite sum of the exact outcome probabilities over
all successful `ω`; the success threshold is inclusive `≥ 1−δ`. It is not
enough to preserve one vector, obtain the bounds in expectation, or allow
the sampled matrix to depend on the test vector.

## Original assertion and resolved negation

For **each fixed** `p>2`, the original positive claim asks whether there
exist `C_p,c_p : ℝ` with `C_p>0` and `c_p>0`, chosen before the matrix and
tolerances, such that for **every** full-column-rank `A` and every
`0<ε,δ<1/2`, **some** `α>0` gives both the size bound

```text
∑_i q_i ≤ C_p · ε^(−2) · (S(A,p)+d) ·
          (log(2*n*d/(ε*δ)))^(c_p)
```

and success probability `≥1−δ` under the prescribed independent sampler.
Here logarithm is natural, its argument is greater than one on the stated
domain, the exponent `c_p` is a real positive constant, and `d` denotes the
number of columns embedded into the reals. There is no hidden dependence on
`n,d,A,ε,δ,α` in either constant. The size and success guarantees must hold
for the **same** choice of `α`.

The published Solved resolution is the **full negation for every exponent**:

```text
∀ p : ℝ, p > 2 → ¬ OriginalPositiveClaim(p).
```

Equivalently, for every `p>2` and every proposed positive `C_p,c_p`, there
are admissible dimensions, a full-rank matrix, and admissible `ε,δ` such
that **every** `α>0` violates at least one of the two displayed
requirements. A Lean `Target : Prop` should state this negation using the
concrete definitions above, not hide it behind an unconstrained
`Success`, `Sampler`, or `Sensitivity` parameter. The original positive
claim should remain as a separately named, readable proposition so the
negation's full quantifier order is inspectable. The theorem does not assert
that nearly linear sensitivity dependence is impossible at fixed accuracy,
nor does it concern unrestricted linear sketches.

## Source's explicit counterexample and numerical witnesses

For the resolution's constructive companion, let `v ≥ 3`, put
`n = binom(v,2)` and `d = v−1`, orient every edge of the complete graph on
`v` vertices, and delete one vertex column from its edge–vertex incidence
matrix to obtain a full-column-rank `A_v`. Grounding one potential
coordinate at zero does not remove any all-vector test. Every row has the
**same** sensitivity

```text
s_v = 1 / (1 + (v−2)·2^(1−p)),
S(A_v,p) = binom(v,2) · s_v,
S(A_v,p)+d ≤ (2^(p−2)+1) v.
```

Consequently the specified rule has one common probability
`q = min {1, 1/n + s_v/α}` for any `α>0`. Keep both the floor and the
saturated branch `q=1`. If

```text
v−1 ≥ 6^(−p) ε^(−(p+1)),
```

then **even one** successful retained graph under a common `q∈(0,1]`
forces the deterministic expected-size parameter to satisfy

```text
n q ≥ (6^(−p)/3) · v · ε^(−p)
    ≥ [6^(−p)/(3(2^(p−2)+1))] · (S(A_v,p)+d) · ε^(−p).
```

This has **no** `1−δ` factor: it constrains `q` upon existence of one
successful realization, rather than lower-bounding expected realized
support only on a success event. The source also proves a stronger
arbitrary-nonnegative-weight support obstruction, but the common-probability
bound suffices for the original sampler's negation.

For an explicit contradiction sequence, take integers `b≥3`,
`ε=b^(−1)`, `δ=1/4`, and `v=⌈b^(p+2)⌉`. For sufficiently large `b` the
dimension regime above holds. Any `α` giving positive success probability
then needs expected size of order at least `v b^p`, whereas the asserted
budget is at most a `p,C_p,c_p`-dependent constant times
`v b² (log b)^(c_p)`. Their ratio grows because `p>2`. The actual target
is the full negation above, not merely a theorem for this one selected
`ε`, a fixed `p`, or an unspecified sampling scheme.

All expressions are exact real or finite sums/products. Defining this
statement requires no exhaustive enumeration of the `2^n` outcomes, no
numerical estimate, and no floating-point calculation. If later proof
certificates are used, they must follow the pinned LeanCert kernel mode;
they are not needed to state the negative proposition.
