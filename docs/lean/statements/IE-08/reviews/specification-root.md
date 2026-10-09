# IE-08 independent specification review

**Verdict: APPROVE** for statement implementation. The specification author
is `/root/fr05_review`; I independently compared it with the canonical page
and full mathematical source. This is not a Lean implementation or proof
review.

## Inputs

Published base: `0e916df335209819b5bf9bb8ed8f65ea978c049d`.

| Input | SHA-256 |
| --- | --- |
| `eigenvalues-and-inverse-problems/IE-08/README.md` | `22dd77f1baaa4004bb8c05ec34c63bffabf99103d48ecfb9fcec92d1bdcc4e7d` |
| `docs/lean/statements/IE-08/ORIGINAL.md` | `22dd77f1baaa4004bb8c05ec34c63bffabf99103d48ecfb9fcec92d1bdcc4e7d` |
| `docs/lean/statements/IE-08/NUMERICAL_TARGETS.md` | `31b774bae370d55c6575397db6c4b3dbad447a9205f3ab2549a96fd85b2bba08` |
| `eigenvalues-and-inverse-problems/IE-08/solution.md` | `650053dc10070ada37746a7fbb5a0d4735de967cc4452d5d03f771216a3e379d` |

`ORIGINAL.md` matches the complete canonical README byte for byte. I read
solution.md Theorem 1 and its computational model (lines 18–45), finite
sampler (288–308), capped levelwise algorithm (439–458), and final work,
probability and residual estimates (535–576).

The specification retains one uniform randomized floating-point algorithm,
all positive dimensions, all `0<δ<1/2`, and every complex matrix of spectral
norm at most one. It keeps universal polynomial-log work and logarithmic
mantissa bounds on **every execution**, not just in expectation or on
success. It requires finite unbiased bits, rounded real operations and
input representation at the selected precision, adaptive finite control
flow, capped loops, and sufficient exponent range. An abstract exact-real
oracle or an unsupported `RunsInTime` label would not meet this contract.

The output is a pair of stored complex matrices with exactly upper
triangular `T`. One joint event of probability at least `99/100` carries
both weak spectral residual bounds against the original `A`. No spectral
gap or diagonalizability restriction is added; the scalar `n=1` case and
arbitrary nonnormal inputs remain in scope. The source's large internal
`R` and `u` exponents are correctly recorded as a witness rather than new
public premises. I found no substantive mismatch. The eventual Lean
boundary must provide concrete operational semantics and receive separate
independent review before any verified-statement claim.
