# SP-14 pre-statement mathematical and numerical review

**Reviewer:** `/root/next_solved_triage` (AI agent), 9 October 2026.
**Phase:** Exact specification before any SP-14 Lean statement or proof is
implemented. A second independent review must approve this specification
before implementation. This document does not certify the 2,118-line source
proof in Lean.

## Permanent identity and reviewed sources

`problem_ids.json` maps the permanent ID `SP-14` to the canonical
`eigenvalues-and-inverse-problems/SP-14/README.md`. The current page has
status **Solved** by a negative resolution. Its complete original conjecture,
including every hypothesis and test function quantifier, remains in the
`## Statement` section after the new resolution. No ID, canonical page, or
historical target is changed here.

| Repository-relative path | Raw-byte SHA-256 |
| --- | --- |
| `eigenvalues-and-inverse-problems/SP-14/README.md` | `9d0c6376080838ea50e8736cb4249276c06a528479fb9c9f565cc7747a485075` |
| `eigenvalues-and-inverse-problems/SP-14/problem.tex` | `286ef6caa3b4e3fce192d8fe133279c98e2d0bdcf3771c6c2969e7c1a58e0957` |
| `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/README.md` | `33b422a65e5d9c0b6e81482ff0505d949a7ffcdfed15dd312cd4c75ce259dca2` |
| `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/verification/independent-review-2026-10-09.md` | `8fd49126378e6d05e28db4e336fe397ee7dc9dc9a17bbe554fe0f7d6df9a7849` |

Repository HEAD at this review was
`95d83131f3a4fff6a2f16194cefcc447a8729e07`. The source paper hash
agrees with the hash named in the archived independent review and submission
record. Those sources are an informal mathematical review and a proposed
proof, not a Lean proof. The independent review expressly did not recompute
the full constant ledger or reprove two central analytic propositions line by
line.

## Exact original conjecture

Let `𝕋 = {z : ℂ | |z| = 1}`. The quantified symbol is **every** continuous
complex-valued `a` on `𝕋`. For each integer `k`, define the Fourier
coefficient with the exact sign and normalization

```text
aₖ = (1/(2π)) ∫₀²π a(eⁱᵗ) e^(−ikt) dt.
```

For every natural `n ≥ 1`, `Tₙ(a)` is the `n × n` complex Toeplitz matrix
whose row `j`, column `k` entry is `a_(j−k)`, with indices `0,…,n−1`.
There is no conjugation, sign reversal, circulant wraparound, or matrix
normality premise.

An **inner** annular extension means there exist `0 < r < 1` and a complex
function holomorphic on `r < |z| < 1`, continuous through the unit-circle
boundary from that annulus, and equal to `a` on `|z|=1`. An **outer**
extension analogously uses some `R > 1`, the region `1 < |z| < R`, and
continuity through its inner unit-circle boundary. The conjecture assumes
**neither** extension exists. It does not assume a Jordan-curve range,
nonzero winding, real-valued symbol, or Tilli-class geometry.

The conclusion quantifies over **every** continuous compactly supported
`F : ℂ → ℂ` and asserts the **full-sequence** complex limit

```text
lim_{n→∞} (1/n) Σ_{λ root of charpoly(Tₙ(a))} F(λ)
  = (1/(2π)) ∫₀²π F(a(eⁱᵗ)) dt.
```

The roots are a multiset: a root of algebraic multiplicity `h` occurs `h`
times. The conjecture is one-way: lack of both extensions implies canonical
distribution. It does not assert that the presence of an extension always
causes failure. The negative Solved target is the **negation of this whole
closed universal proposition**. Proving a counterexample in only a restricted
Jordan or finite-symbol class, or disproving convergence only for a different
matrix sequence, would not settle this original target.

## Proposed faithful Lean boundary

This is a design contract, **not implemented Lean code**. Prefer a unit-circle
subtype `Circle := {z : ℂ // ‖z‖ = 1}` and a continuous function
`a : Circle → ℂ`. Define a circle parametrization
`circleExp(t) = exp(i t)` with a proof that its norm is one. Use the complex
interval integral in the Fourier formula above, with `k : ℤ` and the genuine
integer power `circleExp(t)^(-k)`. The real interval `0..2π` and factor
`1/(2π)` must remain explicit, or be replaced only by a proved equality
with normalized Haar measure.

Define `InnerExtension a` and `OuterExtension a` by **existence of actual
functions** on `ℂ` with `DifferentiableOn ℂ` on the respective open annulus,
`ContinuousOn` on its one-sided closure at `|z|=1`, and boundary values equal
to `a`. An uninterpreted extension flag or a Fourier-decay proxy without a
proved equivalence is insufficient. No continuity or boundary value is
required at the other radius `r` or `R`.

Define `Toeplitz a n : Matrix (Fin n) (Fin n) ℂ` by the coefficient
`a_(row−column)`. Define `Eigenvalues a n` as the multiset of complex roots
of the **characteristic polynomial** of that matrix. This captures
algebraic multiplicity even when the matrix is nonnormal or nondiagonalizable.
The empirical average is the root-multiset sum divided by the actual `n`,
for `n ≥ 1`. The value at `n = 0` may be arbitrary because an `atTop`
limit is insensitive to it; using `n+1` everywhere is equivalent only after
an explicit index-shift proof.

The declarations should have this logical shape:

```text
OriginalConjecture :=
  ∀ a : Circle → ℂ, Continuous a →
    ¬ InnerExtension a → ¬ OuterExtension a →
    ∀ F : ℂ → ℂ, Continuous F → HasCompactSupport F →
      Tendsto (fun n => EmpiricalAverage a F n) atTop
        (nhds (CanonicalAverage a F))

Target := ¬ OriginalConjecture
```

Use an explicit source-witness proposition and theorem as an independently
checked **stronger** companion, then derive `Target`. The source witness
should quantify an actual continuous `a` with neither extension and a
strictly increasing sequence `m_j` of naturals, set `n_j = 2m_j+1`, and
assert both characteristic-polynomial root counts

```text
mult_{T_(n_j)(a)}(+1) ≥ floor(θ m_j),
mult_{T_(n_j)(a)}(−1) ≥ floor(θ m_j),
θ = 2^(−10000) > 0.
```

It should also retain that both `+1` and `−1` lie outside `a(𝕋)`. For the
particular test below, include or prove the stronger separation
`∀ z : 𝕋, |a(z)−1| ≥ 1/8` (the source proves a strict margin). The source
proof constructs a **computably specified** symbol, but computability is
extra strength and is not a premise of the original conjecture; it should
not be used to narrow the universal `OriginalConjecture`.

## Source counterexample and numerical checkpoints

Thalhammer's Theorem 6.1 gives the above odd orders and multiplicities. Its
base symbol is `a₀(z)=√(z²+1)` on the circle; exactly

```text
charpoly(T_(2m+1)(a₀))(w) = w (w²−1)^m.
```

This base has an outer annular extension and therefore is **not itself** a
counterexample to the original conjecture. The final symbol has the form
`a(z)=z g(z²)` with `g(s)=√(1+s⁻¹)+P₋(s)+P₊(s)`; positive packets destroy
outer extension and untouched negative binomial coefficients destroy inner
extension. Later-stage Fourier support leaves earlier selected Toeplitz
sections unchanged. The source's explicit construction parameters include

```text
γ=2^(−1000), θ=2^(−10000), σ=3/8, m₀=2^10000,
κ=2^(−1010), β_j=γ 2^(−j−4),
q_j=3m_j/8, h_j=floor(θ m_j), n_j=2m_j+1.
```

The source chooses each `m_j` divisible by eight and at least eight times
the preceding order. Its packet scale is
`τ_j=κ 2^(−ceil(sqrt(2m_(j−1)+1)))`. These are proof-construction
invariants, not additional hypotheses on the original symbol. A Lean proof
can use a different exact construction only if it still proves the full
negative `Target`; finite-order numerical experiments alone cannot do that.

For the concrete test function, use a **real-valued**
`φ(w)=max(0, 1−8|w−1|)` and the complex-valued `Φ(w)=(φ(w):ℂ)`.
Its support lies in `|w−1|≤1/8`; it is continuous, compactly supported,
nonnegative, and `Φ(1)=1`. The base range has
`dist(±1,a₀(𝕋))=√2−1`. The final uniform perturbation is less than
`2γ`, so `dist(1,a(𝕋))≥√2−1−2γ>1/8`; hence
`Φ(a(z))=0` for **every** `z∈𝕋`, and the canonical integral is zero.
Merely knowing `1∉a(𝕋)` would not suffice for this exact `Φ`.

At selected order `n_j=2m_j+1`, nonnegativity of `φ` and the root count
give the exact finite lower bound

```text
EmpiricalRealAverage(a, φ, n_j)
  ≥ floor(θ m_j)/(2m_j+1).
```

Because `m_j→∞`, the **lower bound** tends to `θ/2 > 0`; therefore
`liminf_j EmpiricalRealAverage(a, φ, n_j) ≥ θ/2`, while the canonical
average is zero. This disproves the original full-sequence limit. The
fraction `floor(θ m_j)/(2m_j+1)` is strictly **below** `θ/2` at every
finite positive `m_j`; thus the multiplicity theorem alone does **not**
justify a pointwise claim that each empirical average is at least
`θ/2`. The README's resolution wording should be read as the subsequential
asymptotic lower bound; the Lean statement must use the exact finite
fraction and limiting consequence.

## Implementation and verification gate

There is currently no `NLA.Statements.SP14.Target` and no SP-14 Lean proof.
The statement should first receive an independent second review of the
Fourier convention, one-sided extension semantics, root-multiset
multiplicity, quantifier order, exact constants, and the corrected
subsequential bound. Only then should the live and frozen Lean declarations
be implemented. LeanCert kernel mode and Comparator can check later proof
identity and trust; neither a statement declaration nor the existing
informal and numerical review establishes the theorem.

The source proof's hard obligations include the exact finite Toeplitz
factorization, one-sided Fourier root tests, quantitative conformal
coordinate and inverse estimates, infinite-stage continuity, and the
deterministic certificate search. Keeping powers such as `2^10000`
symbolic avoids giant normalization without changing any numerical target.
