# IE-08 independent pre-implementation specification review

**Verdict: APPROVE.** I independently compared `NUMERICAL_TARGETS.md` with the complete canonical problem and all 589 lines of the authored `solution.md`. This approves the mathematical and operational statement boundary before Lean implementation; it does not certify the manuscript proof or approve a future Lean encoding.

## Inputs and hashes

Published base: `0e916df335209819b5bf9bb8ed8f65ea978c049d`. SHA-256:

| Input | SHA-256 |
| --- | --- |
| `eigenvalues-and-inverse-problems/IE-08/README.md` | `22dd77f1baaa4004bb8c05ec34c63bffabf99103d48ecfb9fcec92d1bdcc4e7d` |
| `docs/lean/statements/IE-08/ORIGINAL.md` | `22dd77f1baaa4004bb8c05ec34c63bffabf99103d48ecfb9fcec92d1bdcc4e7d` |
| `docs/lean/statements/IE-08/NUMERICAL_TARGETS.md` | `31b774bae370d55c6575397db6c4b3dbad447a9205f3ab2549a96fd85b2bba08` |
| `eigenvalues-and-inverse-problems/IE-08/solution.md` | `650053dc10070ada37746a7fbb5a0d4735de967cc4452d5d03f771216a3e379d` |

`ORIGINAL.md` is byte-for-byte identical to the canonical README.

## Exact-target comparison

The specification preserves one **uniform randomized floating-point algorithm** and universal positive work, precision, and logarithmic-exponent constants before quantification over every `n ≥ 1`, every real `0 < δ < 1/2`, and every complex `n × n` input with spectral norm at most one. The work cap is worst-case `O(n³ log^c(n/δ))`, while mantissa precision is `O(log(n/δ))` **per real component**. No gap, simplicity, diagonalizability, or conditioning premise is introduced. The source's separate `n=1` path remains covered.

The success event is joint on a single execution, at inclusive probability `99/100`, and contains both weak spectral-norm bounds `‖A−QTQᴴ‖₂≤δ` and `‖QᴴQ−I‖₂≤δ`. `T` is exactly upper triangular, including on failure/dummy executions. The output is interpreted as the stored complex matrices, rather than an idealized exact Schur factorization. The specification correctly does not require `Q` to be exactly unitary.

The proposed machine boundary retains the manuscript's ordinary relative-error floating-point arithmetic with real square roots, sufficiently wide exponent range, finite unbiased-bit randomness, finite sample generation, fixed work and bit caps, charged adaptive control flow, and rounded input. It explicitly forbids replacing the algorithm by an arbitrary exact-real function with an unverified cost label, exact Gaussian/eigensolver/matrix-function oracles, unbounded rejection, or hidden multiword precision. The optional dyadic encoding of a real tolerance is presented with an explicit equivalence obligation, not as a restriction to dyadic tolerances. These requirements reflect the computational model in the complete source, especially its finite-sampling and final precision/work audit.

The conservative source witness `R` and `u≤R^(−2000)` is correctly identified as proof-side machinery rather than a new input assumption or fixed public constant. The source's final failure union is strictly below `1/100` and yields the stated inclusive `99/100`; the two residual estimates and exact triangularity are retained. No mathematical or numerical omission requiring correction was found.

**Implementation gate:** a future Lean statement must implement the advertised concrete finite machine, rounding, input interface, and cost semantics. An opaque `Algorithm` type, free `RunsInTime` proposition, or unproved oracle interface would invalidate this approval even if the final theorem type-checks. Review the complete imported meaning and frozen Lean boundary separately.
