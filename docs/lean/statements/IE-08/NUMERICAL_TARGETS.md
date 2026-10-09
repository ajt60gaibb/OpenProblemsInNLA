# IE-08 exact mathematical and numerical target

## Source boundary

The complete original canonical entry is `ORIGINAL.md`, copied byte for byte
from `eigenvalues-and-inverse-problems/IE-08/README.md` at published base
`0e916df335209819b5bf9bb8ed8f65ea978c049d`. Its permanent ID and
canonical path stay unchanged. The affirmative source is Matthew J.
Colbrook's `eigenvalues-and-inverse-problems/IE-08/solution.md`, Theorem 1
and the complete proof (especially lines 18–45 and 439–576). The author's
`solution.tex` and the independent manuscript review are supporting records.
This file specifies the proposition to state in Lean; it is not a proof of
the algorithmic theorem.

## Original guarantee and quantifiers

There must be **one uniform randomized floating-point algorithm** and
universal constants `C,c > 0`, independent of dimension, tolerance, matrix,
random bits, and spectral properties, such that the following holds for
**every** positive integer `n`, every real `0 < δ < 1/2`, and every
`A : Matrix (Fin n) (Fin n) ℂ` with spectral/operator norm `‖A‖₂ ≤ 1`.
The algorithm chooses its precision using its ordinary finite accuracy
input, may adapt its control flow to earlier rounded computations and random
bits, and terminates on every execution. Its worst-case, not expected,
arithmetic count is at most

```text
C · n^3 · (log(n/δ))^c,
```

and it uses at most `C · log(n/δ)` mantissa bits **per real component**.
The base of `log` may be fixed to the natural logarithm: changing base
only changes universal constants. Here `n/δ > 2`, so the logarithm is
positive. One may use separate positive universal work and precision
constants and then take their maximum. One may use a positive integer
logarithmic exponent after increasing it and the universal coefficient;
this is equivalent to the original existential exponent on this domain.
Neither a dimension-dependent exponent nor an input-dependent hidden
constant is allowed.

Every returned object consists of two stored complex `n × n` matrices
`Q,T`, interpreted as exact complex matrices when testing the output.
`T` is **exactly upper triangular**: every entry strictly below its main
diagonal is zero, including on an abort/dummy path. With probability at
least the exact rational number `99/100`, the **same run** satisfies both
weak spectral-norm residual inequalities

```text
‖A - Q*T*Qᴴ‖₂ ≤ δ,       ‖Qᴴ*Q - I‖₂ ≤ δ.
```

`Qᴴ` is conjugate transpose. The claim does not require `Q` itself to be
exactly unitary, nor does it accept a bound on just one residual. The
probability is over the algorithm's finite unbiased random bits; the
resource caps hold on unsuccessful runs too. No distinct-eigenvalue,
eigenvalue-gap, diagonalizability, condition-number, or other input
promise is permitted. The source handles `n = 1` separately and covers
all `n ≥ 2` by its regularized recursive construction.

## Operational floating-point and Turing boundary

The phrase “randomized floating-point algorithm” is an essential part of
the proposition. A Lean statement must not replace it with an arbitrary
random function from exact `A` to `(Q,T)` plus a claimed cost number. Use a
defined finite instruction/transition semantics, or an equivalently
concrete computable machine encoding, with all of these properties:

1. Scalar arithmetic uses the usual relative-error floating-point model
   at a selected integer mantissa precision: each real addition,
   subtraction, multiplication, division, and real square root is rounded
   according to one fixed implementation/rule and satisfies its standard
   relative-error bound when defined. Zero and structural zero assignments
   are exact. Complex arithmetic expands to a constant number of real
   operations. Comparisons, bit operations, branching, indexing, loops,
   and memory updates are finite machine actions, not exact-real oracles.
   The exponent range is sufficiently wide to avoid overflow and
   underflow; it must not serve as hidden multiword exact precision.
2. Arbitrary complex `A` is supplied through ordinary input rounding at
   the chosen precision. The guarantee is measured against the original
   mathematical `A`, so input conversion error must be accounted for.
   Likewise `δ` is a finite accuracy request, not an oracle for arbitrary
   exact-real computation. A precise Turing interface may accept a dyadic
   encoding `δ̃` with `δ/2 ≤ δ̃ ≤ δ` and prove the bridge to every real
   requested `δ`; then the machine uses `δ̃` and the resource bounds are
   still expressed in `log(n/δ)`. This representation choice requires an
   explicit equivalence argument before claiming the original target.
3. Randomness consists of finitely many unbiased bits. Each run has a
   deterministic finite bit-consumption cap, so its success probability
   is an ordinary finite uniform probability over bit strings, including
   abort paths. Random sample generation, grid offsets, transcendental
   approximations, matrix operations, and all retries or loops are charged
   to the capped work. No ideal Gaussian sample, exact eigensolver,
   matrix-sign oracle, unbounded rejection loop, or multiword
   high-precision simulation may be treated as a primitive.

These clauses preserve the adaptive randomized floating-point/Turing cost
model in the manuscript (solution lines 28–45, 288–308, 439–458, and
535–576). A model with an uninterpreted `Algorithm` type, an unproved
`RunsInTime` label, or an exact-real branch operation would make the
statement materially weaker.

## Source's numerical witness and status

The theorem is asymptotic: it does not prescribe a numerical value for the
universal `C` or `c`. The proof chooses a dyadic `R` within a factor of two
of `max {2^40, C₀^100, 10^24(n/δ)^10}` and unit roundoff `u ≤ R^(-2000)`
(solution equations (13)–(14), lines 272–286), then caps all iterations,
sampling, and aborts. Its final failure union is less than `1/100`
(lines 535–543), and its two output bounds are completed in lines 547–576.
These internal exponents are one conservative witness for the public
asymptotic claim, not extra input assumptions or a replacement target.

The author's output is a backward Schur approximation. The target is not
merely an exact Schur factorization over ℂ with no operational cost, an
approximate triangularity assertion, an eigenvalue-only answer, or a
statement for already separated matrices. An eventual proof may simplify
internal kernels and use equivalent finite encodings, but must retain the
uniform algorithm, actual precision and worst-case work bounds, exact
triangular output, the joint `99/100` event, and both original residuals.
