# Independent informal audit of SP-08

**Date:** 2026-09-12. **Reviewer:** OpenAI Codex independent reviewer agent
`review_sp08`, separate from the submitting/editor agent. This is an AI-agent
informal audit with freshly executed exact computations, not external human peer
review or formal verification. No Lean verification was requested or performed.

**Verdict: PASS for the signed-threshold reduction and the three stated finite
cases; NOT a complete resolution of SP-08. Retain `Partially resolved`.**

I reviewed the supplied `SP-08/proof.md`, all three certificate JSON files, the
main verifier and both secondary checkers against the canonical SP-08 statement,
CONTRIBUTING.md and RESOLVED.md. The reviewed input hashes are recorded in
[SP-08-reviewed-sha256.json](SP-08-reviewed-sha256.json). Original submission
self-review assertions and historical logs were not treated as independent
evidence. Authorship metadata and later editorial formatting do not change the
mathematical argument reviewed here.

## Mathematical correspondence

The original target quantifies over every order n >= 2 and every normalized
interval parameter -1 <= a < 1. It includes free diagonal entries and asks for
existence of a rank-exactly-two endpoint maximizer. The submission respects all
of these conventions but proves attainment only for (n,a) = (8,1/2), (10,0),
and (11,0), with maximum spreads sqrt(73), sqrt(133), and sqrt(161).

Theorem 1 passes. The difference of extremal Rayleigh quotients exposes a linear
functional on the symmetric entry box. Its factorization as uv^T + vu^T allows
arbitrarily small perturbations with nonzero denominator coordinates and
distinct, nonzero absolute coordinate ratios. Ordering these ratios makes the
larger absolute ratio determine each off-diagonal sign; the diagonal follows
the same rule. Global reversal fixes the first sign without losing matrices.
Permutation similarity preserves spread and the box, so no permutation factor
is required in the enumeration. A constant subsequence from the finite endpoint
set transfers optimality back to the possibly degenerate original functional.
The perturbed vectors need not remain eigenvectors or orthogonal: only linear
functional optimality is used before taking the limit. This closes the important
zero-entry and tied-ratio cases.

The root-bound lemma passes: a monic polynomial with nonnegative coefficients
is strictly positive at every positive argument. Applying the scaled shift to
p and its monic negation bounds both extreme real eigenvalues. A nonnegative
rational width whose square is at most F establishes the claimed upper bound.
The separate quadratic certificate correctly handles equality and zero roots.

The block attainers pass: the two-dimensional compression has determinant
(a-1)k(n-k) < 0, and the orthogonal complement is annihilated. Thus their rank
is exactly two, with opposite-sign extreme eigenvalues. Substitution of block
sizes 2, 3, and 4 gives the stated spreads. Scaling entries {1,2} by 1/2 divides
squared spread by four, converting the order-eight bound 292 to 73.

## Exact implementation and fresh execution

I inspected bit enumeration, Newton identities, polynomial shifting, sign
negation, set equality and overflow checks. The bit split exhausts n epsilon
signs and n-1 independent d signs. Coverage compares the complete coefficient
sets, not only their hashes. Symmetry bounds eigenvalues by nb; coefficient and
trace bounds give n*2^n*(nb)^n as a valid bound for all partial Newton sums.
Absolute matrix powers also bound partial dot products, so the checked int64
bound excludes overflow for these three inputs. Root-certificate arithmetic
uses Python arbitrary-precision integers. The verification path does not call
a floating-point eigensolver.

Fresh runs used bundled Python and NumPy 2.3.5. All commands exited successfully:

| Case | Exhaustively regenerated patterns | Distinct polynomials | Integer squared-spread upper bound | Log |
|---|---:|---:|---:|---|
| n=8, entries {1,2} | 32,768 | 5,648 | 292 | [Full run](SP-08_n8_a-half-independent.log) |
| n=10, entries {0,1} | 524,288 | 65,077 | 133 | [Full run](SP-08_n10_a0-independent.log) |
| n=11, entries {0,1} | 2,097,152 | 222,013 | 161 | [Full run](SP-08_n11_a0-independent.log) |

Each main run recomputed the entire pattern family and checked every root
certificate. It also cross-checked one matrix per batch using scalar
arbitrary-precision Faddeev-LeVerrier arithmetic. I additionally reran the
supplied direct-binomial implementation for every root certificate in all
three files: [secondary root-check log](SP-08-binomial-independent.log).
Finally I reran the scalar integer implementation on all 5,648 order-eight
representatives: [secondary characteristic-polynomial log](SP-08-n8-reference-independent.log).
The latter two checkers are different supplied implementations audited and
executed by this reviewer, not independently authored reviewer programs. The
full scalar representative test was not repeated at orders ten and eleven.

From the archived submission's SP-08 directory, reproduction is:

```bash
python3 verification/spread_exact.py verify certificates/SP-08_n8_a-half.json
python3 verification/spread_exact.py verify certificates/SP-08_n10_a0.json
python3 verification/spread_exact.py verify certificates/SP-08_n11_a0.json
python3 verification/check_taylor_certificates.py certificates/SP-08_n8_a-half.json certificates/SP-08_n10_a0.json certificates/SP-08_n11_a0.json
python3 verification/reference_integer_check.py certificates/SP-08_n8_a-half.json
```

## Bounded prior-art check and policy decision

On 2026-09-12 I checked the [arXiv version history](https://arxiv.org/abs/2510.15919)
(only v1 listed), [Calkin et al., Sections 1, 3.2, 7–8 and 10](https://arxiv.org/html/2510.15919v1),
and the [authors' supporting repository](https://github.com/rcorless/BohemianSpread).
The paper records all parameters through order seven, a=0 through order eight
and orders divisible by three, and an unclosed gap in its general approach.
Its block candidate formula already supplies the lower-bound construction used
here. The supporting repository advertises the same finite ranges.
Searches for `"spectral spread" "signed" "threshold"` and
`"Fallat" "Xing" conjecture 2026 proof` did not locate a subsequent complete
resolution or the same signed-threshold reduction. This bounded search does
not establish publication novelty or priority; no such claim is approved.

The three cases go beyond the ranges explicitly listed by those sources and
the inspected canonical README. Whether another already-pushed repository
submission duplicates them is a separate submission-history check for the
editor, not an inference from this literature search.

Under RESOLVED.md's partial-result rule, the approved update can cite Theorem 1
and the three exact subcases with this report. It cannot mark SP-08 `Solved`:
the submission supplies no all-orders argument that a signed-threshold
maximizer has rank two. The canonical ID, path and all-parameter target must
remain unchanged.
