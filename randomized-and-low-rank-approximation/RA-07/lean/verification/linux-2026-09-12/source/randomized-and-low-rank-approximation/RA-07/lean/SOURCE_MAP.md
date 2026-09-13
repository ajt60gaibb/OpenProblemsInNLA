# RA-07 source correspondence

Source commit: `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`.
The retained canonical problem and complete Colbrook manuscript were read before
writing the numerical targets and Lean signatures. They match their Git blobs.

| Source file | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-07/README.md` | `895569df92c91c035ba57817b1e833a4369072bb73c550bd8c79f7890d02d11d` |
| `references/colbrook-transfer-2026-09-11/manuscripts/01_volume_sampling_convexity.tex` | `12d83b342f9f069cf1a623b4dffe6ee6d6abb1c5d0a9d001f4713777b5beef01` |
| `references/colbrook-transfer-2026-09-11/verification/reviews/RA-07-review.md` | `a4b10d377c422788379189dfd4875e6060ceb9142675a55c8c50b81fd6cda383` |

The mathematical source is Theorem 1.1 in *Convexity of a volume-sampling error
sequence* by Matthew J. Colbrook. The proof-development author is George
Stepaniants, Department of Computing and Mathematical Sciences, California
Institute of Technology, Pasadena, California, USA, with AI-agent assistance.

| Formal declaration | Source obligation and scope |
| --- | --- |
| `elementary_values` | The actual empty-subset sum is 1, oversized subsets contribute 0, all admissible elementary sums are positive. |
| `generating_derivative_values` | Actual product-polynomial coefficients and iterated derivatives at zero give `e_j` and `j! e_j`, for every natural index. |
| `positive_derivative_factorization` | Every derivative of order `d≤n` has positive constant term, degree `n−d`, and exactly `n−d` positive reciprocal-root factors including multiplicities; no factorization is assumed. |
| `power_sum_certificate` | `s1 s3−s2²` is the sum of nonnegative unordered-pair terms, and `s1(s1²−s2)>0` when at least two positive factors remain. |
| `second_difference_certificate` | The unconditional exact certificate for the actual ratios at each original index `j`, using derivative order `j−1` and factor count `n−(j−1)`. |
| `errorSequence_convex` | Complete original assertion for every `n≥3`, every positive real tuple, and every `2≤j≤n−1`. |

The Lean identifier `lam` represents the mathematical tuple `λ` (bare `λ` is a
reserved Lean syntax token). The use of zero-based `Fin` coordinates, natural
indices and ordinary real division is explicit; denominator positivity is a
separate proof obligation. A real polynomial factorization is an equality of
actual `Polynomial` values, not a bundled hypothesis or a root table.

The source's strict monotonicity, additional convexity index 1, determinantal
sampling identity, Jensen consequence and stable-rank bounds are not advertised
formal results. Their exclusion does not narrow the canonical target. The
canonical discussion of sampling motivates its exact scalar conjecture; a proof
of that original scalar assertion is the complete requested mathematical answer.

The planned replacement of repeated Rolle arguments by Mathlib Gauss–Lucas
must retain all complex-root multiplicities when converting to a real
factorization. The source of that formal theorem is
`Mathlib/Analysis/Complex/Polynomial/GaussLucas.lean` at Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474` (Yury Kudryashov, Aristotle AI).
Existing `Finset.esymm_map_val`, `Polynomial.coeff_iterate_derivative`, and
`Polynomial.natDegree_iterate_derivative` are the intended subset/coefficient
and derivative APIs. No external literature result is to be assumed as an axiom.

This file maps unproved stage-one statements. Compilation and the exact finite
precheck do not establish a universal proof. Both independent statement
approvals are required before implementation; final reviewers and actual Linux
Comparator/kernel replay remain later gates.
