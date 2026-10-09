# TR-08 exact mathematical and numerical target

This is a **pre-implementation specification**, not a proof or an independent
review. `ORIGINAL.md` preserves the entire canonical
`randomized-and-low-rank-approximation/TR-08/README.md` byte for byte at
published base `0e916df335209819b5bf9bb8ed8f65ea978c049d`. The
resolution is Theorem 1.1 and Sections 2–7 of
`randomized-and-low-rank-approximation/TR-08/solution.tex`.

## Quantified dimensions and exact random law

Let the row dimension `k` tend to infinity **only through positive multiples
of 100**; equivalently, index the sequence by `t≥1` and take `k=100t`.
Fix any real `c>0`. For each such `k`, take an integer ambient column count
`n_k` with `n_k ≥ k^(1+c)` (the inequality is in the reals), and an integer
sparsity `s_k` with `1≤s_k≤k`. The sequences may vary arbitrarily, without
monotonicity. The constant `c` is fixed before the sequences; the theorem
applies to every such `c` and every admissible pair of sequences. The
ambient condition is retained even though the source proves that the
selected submatrix's law no longer depends on `n_k` once selection is
possible.

Construct `M_k : Matrix (Fin k) (Fin n_k) ℝ` by **independent columns**.
For each column `j`, choose a subset `S_j⊆Fin k` uniformly among all
subsets of **exactly** `s_k` distinct rows. These subsets are independent
across columns. Conditional on all supports, give every selected position
`(i,j)` an independent fair sign `ε_ij∈{−1,+1}`, independent of all supports.
Set

```text
M_k(i,j) = ε_ij / sqrt(s_k)  if i∈S_j,
           0                otherwise.
```

The sign magnitude is exactly `1/sqrt(s_k)` and no column has a random
number of nonzeros. Pre-drawing independent signs also at unselected
positions and ignoring them is equivalent. Do **not** substitute Bernoulli
row inclusion, sampling with replacement, a fixed global support, Gaussian
entries, or unsigned columns.

Independently of the **entire** matrix construction, choose `I_k⊆Fin n_k`
uniformly among subsets of **exactly** `m_k=k/100` columns. Form the
`k×m_k` selected submatrix `B_k=(M_k)_:I_k`, using the increasing order of
selected indices or any other deterministic ordering. Column permutations
do not change its singular values. The probability in the theorem includes
both the matrix law and the independent uniform column-subset law. Given
any value of `I_k`, its selected columns are independent and have exactly
the single-column law above; this proves the reduced `k×m_k` product-law
form used in the solution. That reduction must be justified if the Lean
proposition uses it; it may not silently discard the original `n_k,I_k`
construction.

All sample spaces are finite. An exact finite uniform measure/product
measure can define the probabilities symbolically; no exhaustive
enumeration or numerical sampling is needed to state the target.

## Least singular value and success event

For a real `k×m_k` matrix `B`, with `m_k≥1`, define its least singular
value exactly by

```text
σ_min(B) = inf { ‖B x‖₂ : x∈ℝ^(m_k), ‖x‖₂=1 }.
```

The unit sphere is nonempty; this is the usual nonnegative smallest
singular value of a tall real matrix. The event is `σ_min(B_k)≥a` for one
fixed **real** `a>0`, with a weak inequality. This is only a lower
singular-value/injectivity bound. No upper norm, two-sided distortion, or
optimal numerical value of `a` is requested.

For a fixed admissible sequence, the target success property is

```text
∃ a : ℝ, a>0 ∧ Pr{σ_min(B_k)≥a} → 1 as k→∞ through 100ℕ_{>0}.
```

The `a` is chosen **after** the sparsity sequence, then remains independent
of `k`, `n_k`, and the realized matrix. The source gives the stronger fact
that a common `a(h)` works for every sequence with the same positive lower
ratio `h`; it does not claim one positive `a` works uniformly as `h↓0`.

## Complete necessary-and-sufficient criterion

The exact resolved target is, for **every** fixed `c>0` and every
admissible pair `n_k,s_k` as above,

```text
(∃ a>0, Pr{σ_min(B_k)≥a} → 1)
    ↔ (liminf_{k→∞, 100|k} s_k²/log k > 0).
```

All logarithms are natural; `k≥100` makes `log k>0`. In a Lean
formulation, the right side can equivalently be the exact eventual lower
bound

```text
∃ h>0, ∃ K, ∀ k≥K with 100|k, s_k² ≥ h·log k.
```

Here casts and `s_k²` are real. The equivalence must be stated for
arbitrary sequences, including oscillating ones. A condition involving
only `s_k²=o(log k)` along the **whole** sequence, an eventual lower bound
with an unspecified positive constant in only one direction, or an
exponent-only threshold would be incomplete. In particular, if the
normalized ratio approaches zero along any subsequence, no fixed
`a>0` gives full-sequence success tending to one.

Useful source-side companions are:

1. If `s_k²=o(log k)` along a sequence, then `σ_min(B_k)→0` in probability.
2. For every `h>0` there exists `a(h)>0` such that any sequence with
   `s_k²≥h log k` eventually has `Pr{σ_min(B_k)≥a(h)}→1`.

These are stronger route statements, while the displayed equivalence is
the complete original target. The manuscript supplies a conservative
explicit witness for the second item:

```text
J(b)=b log(100b)−b+1/100,  η=J(1/32)/8>0,
R=ceil(3/(η h))+1,  L=2(R−1),  D=1+128/h,
a(h)=1/(6+8 sqrt(D L)).
```

This witness need not be numerically evaluated to state the main
criterion. The criterion is equivalent to `s_k=Ω(sqrt(log k))`: every fixed
positive multiple succeeds, `sqrt(log k)/log log k` fails, and the result
decides the critical window and oscillating sequences. No monotonicity of
`s_k` and no uniform positive bound across arbitrarily small `h` may be
inserted.

The original statement and source proof use the same finite product law;
their reduction does not authorize replacing the lower singular-value
target with an upper embedding assertion. Later Lean certificates, if any,
must use the pinned LeanCert kernel mode, but no floating-point or large
finite computation is needed merely to define this proposition.
