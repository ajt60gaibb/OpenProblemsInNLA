# TR-21 exact mathematical and numerical target

This is a **pre-implementation specification**, not a Lean proof or a review.
The complete canonical statement and resolution are preserved byte for byte
in `ORIGINAL.md` from `tensor-computations/TR-21/README.md` at published base
`0e916df335209819b5bf9bb8ed8f65ea978c049d`. The resolution is Theorem
1.1 of `references/haidary-resolutions-2026-09-30/TR-21-Seginer-comparison-revised.tex`.

## Tensor format and law

For each **order** `r : ℕ` with `r ≥ 3`, consider every rectangular format
`n : Fin r → ℕ` with `n j ≥ 2` for every mode `j`. The finite tensor index set
is `I(n) = ∏ j : Fin r, Fin (n j)`. A deterministic tensor is a function
`I(n) → ℝ`. There is no equal-dimension or cubic-format restriction.

For **each** such format, quantify over **every** real-valued probability law
`μ` with `∫ |t| dμ(t) < ∞` and `∫ t dμ(t) = 0`. The common entry law may vary
with `n`. Under the finite product probability law `μ` over `I(n)`, the
coordinate projections `T_i` form an independent identically distributed
array with that law. Equivalently one may quantify over any probability space
and every measurable iid array with this common integrable centered law;
the finite product law preserves the distribution of the complete finite
array and hence both expectations in this target. Do not introduce symmetry,
boundedness, a density, variance normalization, a finite second or higher
moment, or a dimension-independent moment comparison. A heavy-tailed or
sparse law is admissible.

`Integrable` means finite **first absolute moment**, not finite variance.
Because `I(n)` is finite, each norm and fiber maximum below is bounded by
`∑ i ∈ I(n), |T_i|`; consequently all displayed expectations are finite.
The zero distribution is included.

## Injective norm and fibers

For each deterministic real tensor `t : I(n) → ℝ`, define its injective norm
by the exact supremum

```text
inj(t) = sup { |∑ i ∈ I(n), t_i · ∏ j : Fin r, x_j(i_j)| :
               x_j : Fin (n j) → ℝ and
               ∑ a : Fin (n j), (x_j(a))² = 1 for every j }.
```

Every factor vector is a **real** Euclidean unit vector; the vectors vary
simultaneously, and the absolute value encloses the complete multilinear
contraction. The feasible set is nonempty, and the supremum is finite. A
matrix flattening norm, Frobenius norm, individual coordinate maximum, or
supremum over a restricted class of unit vectors would change the target.

For a mode `j`, let `I_{-j}(n)` be the finite assignments of one coordinate
`i_h ∈ Fin (n h)` for every `h ≠ j`. For `u ∈ I_{-j}(n)`, let
`insert_j(u,a) ∈ I(n)` agree with `u` off mode `j` and have coordinate `a`
at mode `j`. The samplewise largest Euclidean **fiber** norm in mode `j` is

```text
fiberMax_j(t) = max_{u ∈ I_{-j}(n)}
                  sqrt(∑ a : Fin (n j), t_(insert_j(u,a))²).
```

The exact comparison quantity is

```text
F(T) = max_{j : Fin r} E_μ[ fiberMax_j(T) ].
```

The maximum over fibers is **inside** the expectation; the maximum over
modes is **outside** the expectation. Replacing this by an expected maximum
over modes, by a maximum of expected norms of fixed fibers, or by a sum of
mode contributions would alter the original target. Each mode has at least
one fiber, so the finite maxima are genuine maxima.

## Original and resolved assertions

The original conjecture asks whether, for **every fixed** `r ≥ 3`, there
exist finite real constants `c_r,C_r` with `0 < c_r ≤ C_r`, chosen before the
format and law, such that for **all** admissible formats `n` and **all**
admissible iid centered integrable real laws `μ`,

```text
c_r · F(T) ≤ E_μ[inj(T)] ≤ C_r · F(T).
```

The constants may depend on `r` and on nothing else: not dimensions,
aspect ratios, the common entry law, tail behavior, or the choice of a
probability-space realization. The entry law is quantified **after** the
format to retain dimension-dependent laws. In Lean, real constants are
automatically finite, but positivity and `c_r ≤ C_r` must be explicit.

The resolution proves the **stronger lower coefficient exactly one**:

```text
∀ r ≥ 3, ∃ C_r : ℝ, 0 < C_r ∧
  ∀ admissible n and μ,
    F(T) ≤ E_μ[inj(T)] ≤ C_r · F(T).
```

Record the complete original existential comparison as the principal
`Target`. The exact lower-one resolved comparison may be recorded as a
separate named companion assertion. If the companion is used to derive the
original, preserve the original quantifier order and `c_r ≤ C_r`; one can
enlarge `C_r` to at least one without changing its order-only dependence.
The `r = 2` matrix theorem and centered Bernoulli specialization are
background/corollary, not replacements for the full `r ≥ 3` target.

No fixed decimal constant or numerical approximation is requested. State
the exact finite-dimensional norms, expectations, and quantifiers
symbolically; no tensor enumeration, floating-point computation, or
probabilistic estimate is needed merely to define the proposition.
