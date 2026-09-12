# MI-29 independent statement review request

Stage 1 is complete. `lake build NLA.MI29.Definitions Challenge` passed with **2710 jobs, exit 0** and exactly five intentional Challenge placeholder warnings. A separate source-elaboration inspection passed and confirms actual `CFC.rpow` / `CFC.abs`, matrix multiplication and star, `MatrixOrder`, and the scoped complex scalar order. No proof module or Solution exists.

The canonical base is `e7252e5307781a7c897bca6cb124f6ab838f6809`. Read the complete MI-29 README, `solution.tex`, and `solution.md`, followed by all three boundary files. The original complete target is positive definite complex A, invertible Hermitian B, arbitrary nonnegative real k,p, and every positive order. The broader semidefinite variant and the known k=2 / B>0 restrictions are outside the negative theorem.

| Boundary | SHA-256 |
| --- | --- |
| `NLA/MI29/Definitions.lean` | `c73bfb1856b3e1059ce2ef1e35f8314cb339edcc38b89d28780d38b122ce1a16` |
| `Challenge.lean` | `7ac10b3c284dc5f86dbbb90ef999d5b210540dd0fbdc0bfc60ee9621d25da3cf` |
| `NUMERICAL_TARGETS.md` | `892449f4f9107661242eca72c50d4f35652a4475ea94573daf2ad865c44e5af2` |

Review priorities:

- Full original quantifiers and admissibility; `IsUnit B` is actual matrix invertibility and B is allowed to be indefinite.
- Explicit unital `CFC.rpow` rather than entrywise powers or nonunital zeroth powers; actual `CFC.abs` and positive Gram square root.
- Correct matrix-order instance and complex-order comparison. Generic determinant reality and positivity are required conclusions, not added assumptions.
- Natural/spectral power agreement and the modulus eighth-power bridge are full proof obligations. No spectral certificate or square-root identity is postulated.
- Exact rational witness A=diag(2,1,1/2), B=(1/5)[[-1,2,0],[2,1,2],[0,2,1]], det B=-1/125 and genuine indefiniteness.
- Correct AB versus BA products, exact two determinant values, positive right-minus-left gap, and full universal negation.
- The optional polynomial certificate is only an implementation aid. Its numerical precheck is not a substitute for the public actual CFC/matrix/determinant claims.
- Only the statement-only build is currently claimed; final kernel proof checks, independent final referees, Linux Comparator, and metadata remain later gates.

Raw build/inspection logs, exact rational precheck, source hashes, and environment metadata are in this reviews directory, with all hashes in `statement-freeze.json`. Please bind each independent scoped verdict to the frozen three-file boundary before proof implementation. Any semantic change requires renewed review.
