# MF-08 independent pre-implementation specification review

Reviewer: OpenAI Codex AI agent `/root/infrastructure`, 2026-10-09. I did not author the MF-08 specification or canonical page. Phase: `specification`. Verdict: **APPROVE** for implementation of the exact Lean statement. This is a statement review, not a proof audit or external human peer review.

## Reviewed inputs

| Input | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-08/README.md` | `f1be500b7a835ccfdaf00db211fe71e27b0fed4108aaf979e4136c95fd656dfe` |
| `docs/lean/statements/MF-08/ORIGINAL.md` | `f1be500b7a835ccfdaf00db211fe71e27b0fed4108aaf979e4136c95fd656dfe` |
| `docs/lean/statements/MF-08/NUMERICAL_TARGETS.md` | `f39c5b22ee0a6689209b898c1aca8175ad567f1b574c62d0272b07820f8b64f7` |

The canonical README and retained `ORIGINAL.md` are byte identical. The permanent ID and canonical path agree with `problem_ids.json`.

## Exact mathematical and complexity comparison

The canonical input is a positive-dimensional rational triple `A : n×n`, `B : n×m`, `C : p×n`, with dimension and rational bits included in the input. The specification preserves that triple and chooses a concrete, complete, row-major, self-delimiting binary encoding. The repository's `BinaryEncoding.encodeNat` and `encodeRat` encode normalized natural and signed rational values; `Complexity.ManyOneNPHard` is already defined using actual finite transducer runs with one uniform polynomial bit-time bound. The specification correctly rejects malformed or trailing input rather than giving it an unmentioned answer. This choice of concrete binary representation does not change the source's rational-input complexity target.

The yes condition retains an **unrestricted real** `m×p` gain matrix `K` and the strict continuous-time Hurwitz requirement on `A+BKC`: every complex eigenvalue has negative real part. The proposed nonzero-eigenvector formulation is equivalent to the finite-dimensional spectrum condition. It excludes imaginary-axis eigenvalues, and introduces no gain bounds, structural pattern, sign condition, or prescribed poles. Ordinary finite matrix products and the exact rational-to-real embedding are required.

The final proposition is NP-hardness of that fixed decision language under polynomial-time **many-one** reductions, with no claim of NP membership or a complexity-class separation. The source's two cited integer subclasses are included in the rational language by denominator-one encoding while retaining the same real gain and Hurwitz condition. The specification does not substitute bounded feedback, generic bilinear inequalities, pole assignment, or a numerical approximation task. There are no analytic tolerances or probability thresholds to preserve. I found no lost quantifier or weakened mathematical target.
