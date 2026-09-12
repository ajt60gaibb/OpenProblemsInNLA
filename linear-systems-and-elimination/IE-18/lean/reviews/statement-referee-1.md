# IE-18 independent statement referee 1

Date: 2026-09-12. Reviewer: OpenAI Codex AI agent `/root`.
The reviewer did not write this project's definitions, Challenge, or numerical
target draft. This is independent AI-agent review, not human peer review.

**Verdict: approve the frozen statement boundary for proof implementation.**
This verdict establishes neither a Lean proof nor a publication-ready status.
The second independent statement approval is also required before implementation.

## Sources and correspondence

I read the complete canonical IE-18 page and Colbrook's complete informal
manuscript at upstream revision `5adea969c17391693978ada2674d25bb5c3daeb1`,
then every line of the proposed definitions, Challenge and numerical targets.
I inspected the actual pinned Mathlib definitions of Hermitian matrices,
positive definiteness, spectrum, the eigenvalue list and greatest elements.

- `FourStepConjecture` retains all dimensions `n≥2`, every nonzero real
  symmetric matrix, and exclusion of 1 from the actual real spectrum. It does
  not impose positive definiteness or a diagonal structure on the universal
  question. Over real entries, conjugate transpose is ordinary transpose.
- `residualCoefficient` is the literal quotient of `vᵀ(I−M)v` by the squared
  Euclidean norm of `(I−M)v`. `residualMap` uses the correct `M` multiplication
  and explicitly returns zero at zero. `fourStepResidual` composes this map
  twice. It assumes no recurrence, denominator certificate, or alleged output.
- `squaredNorm` is the sum of coordinate squares and `euclideanNorm` is its
  nonnegative real square root. This is the actual Euclidean norm, without
  accidentally selecting the default function-space supremum norm.
- `amplificationSet` includes exactly the unsquared norm ratios at all nonzero
  input vectors. Mathlib's `IsGreatest` requires membership and an upper bound
  for every member. This faithfully encodes the original maximum identity;
  there is no totalized supremum over a possibly empty or unbounded set.
- The eigenvalues used by `pairMaximum` are Mathlib's actual full list from
  the Hermitian spectral theorem. The associated eigenvector basis is indexed
  by the matrix index type, and `eigenvalues_mem_spectrum_real` and
  `spectrum_real_eq_range_eigenvalues` connect that list with the actual
  spectrum. A hypothetical user-supplied spectral certificate is not assumed.
- The finite maximum ranges over all distinct index pairs, retaining
  eigenvalue multiplicity. The NNReal norm squared is the real scalar square.
  Zero denominators give zero by real division, as specified by the canonical
  convention. For `n≥2` the distinct-index set is nonempty. The use of `a−1`
  inside an absolute value agrees with the source's equivalent `1−a` form.
- The square in the pairwise expression belongs to the proposed *unsquared*
  norm ratio. The reviewed obligations correctly compare the squared norm
  ratio to a second square, namely `1/14641`, before deriving the unsquared
  strict violation.
- The extra positive-definiteness assertions concern only the concrete witness
  and appear as conclusions, not hypotheses narrowing the original question.
  Both residual denominator values are positive; totalized division cannot
  create the numerical violation. The genuine spectrum and genuine pairwise
  maximum must be proved, not replaced by candidate values in the definitions.
- An actual amplification strictly above the proposed maximum disproves its
  greatest-element assertion and therefore the complete universal conjecture.
  The parameter-family underestimation theorem and the separate asymptotic
  convergence question are explicitly excluded, with no claim they were proved.

## Independent numerical reconstruction and type checking

I reconstructed both residual-map applications from exact Python rational
arithmetic, starting only with the diagonal matrix and `(1,1,1)`. This independently
gave denominators `61/50` and `1381/93025`, coefficients `90/61` and `3140/1381`,
and residuals `(-2,8,15)/61` and `(289,-756,1125)/84241`. All three unordered
pair values are `1/289`, `1/121`, and `9/2401`. Thus the proposed factor is
`1/121`, its square is `1/14641`, and the actual squared ratio is
`1920682/21289638243`, strictly greater. The reconstruction record is
[statement-referee-1-numerics.json](statement-referee-1-numerics.json).
This supplementary calculation is not a Lean proof.

I independently ran `lake build NLA.IE18.Definitions Challenge`: exit 0,
2645 build graph jobs with cached dependencies. The only reported placeholders
were the three intentional Challenge declarations. I did not implement or
claim any solution proof during this review. No numerical, domain, or semantic
mismatch was found. Exact diagonal algebra and square comparisons can avoid
numerical eigenvalue computation, sphere optimization, and interval subdivision.

## Frozen inputs

| File | SHA256 |
|---|---|
| `NLA/IE18/Definitions.lean` | `dc32a03d0ab95a1b3f41f864f90d30d56c3dd041330015caa059e253ff47b28d` |
| `Challenge.lean` | `97ad7cf8e2c3077d4cc52f587c9702627f06c8d915005804f044fd60c66ffd59` |
| `NUMERICAL_TARGETS.md` | `318f34ec1f88f111a83c1a6c869735ac2cc5640b5bdb34f89201e97607e9e890` |
| Canonical README at the pinned base | `ef32afd5788f56db1295284fba30de95e56478669f16513daed47535447ab7f0` |
| Complete Colbrook TeX at the pinned base | `f7ebc6b6ebed015e24dfae48b0ed525fe67c99530a35ba66bed7d6ba44aa6b36` |

Original informal proof authorship remains Matthew J. Colbrook's; George
Stepaniants receives formalization credit and his department/university
affiliation. The statement gate follows the relevant Tau Ceti fidelity,
scope, documentation and attribution principles. Final independent proof
reviews, axiom closure, Comparator identity/kernel checks and immutable
publication evidence are separate gates still to be completed.
