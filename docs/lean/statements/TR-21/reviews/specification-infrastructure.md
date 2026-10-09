# TR-21 independent specification review

Reviewer: OpenAI Codex AI agent `/root/infrastructure`, 2026-10-09. I did not author the canonical page, the specification, or the Lean boundary. Phase: `specification`. Verdict: **APPROVE** for implementation of the complete original target. This is a statement review, not a proof review or human peer review.

## Bound inputs

| Input | SHA-256 |
| --- | --- |
| `tensor-computations/TR-21/README.md` | `645fab1674f258c7d120c880118f296ab2066b25ddd257e55bd5b1ad2e84e764` |
| `docs/lean/statements/TR-21/ORIGINAL.md` | `645fab1674f258c7d120c880118f296ab2066b25ddd257e55bd5b1ad2e84e764` |
| `docs/lean/statements/TR-21/NUMERICAL_TARGETS.md` | `8f8266b6106deb2648aacc0ffc6f50801d49c076d5c4638897d5d6606a39f0f4` |
| `references/haidary-resolutions-2026-09-30/TR-21-Seginer-comparison-revised.tex` | `7beed83c0e2d8b9fc2b02c8203cb6d94317270044b5e14dfb9e1ecb4a1456393` |

The retained `ORIGINAL.md` and canonical README are byte identical (`cmp` passed) at published base `0e916df335209819b5bf9bb8ed8f65ea978c049d`. The permanent registry path remains `tensor-computations/TR-21/README.md`.

## Mathematical comparison

The page asks, for each fixed order `r ≥ 3`, for two positive finite constants chosen before all rectangular dimensions `n_j ≥ 2` and before every iid centered integrable real entry law. The specification retains this quantifier order. In particular, selecting the law after the dimensions allows sparse or heavy-tailed laws whose parameters depend on the dimensions. Its finite product realization has precisely the iid joint law of the complete finite array, so it does not restrict the conjecture to a special probability space.

The specified injective norm uses a real Euclidean unit vector in each mode, the complete multilinear contraction, and the absolute value after summing every tensor entry. Its mode-`j` fiber fixes every other index, takes the Euclidean norm, and maximizes across fibers for each sample. The specification places the expectation after this fiber maximum and the maximum across modes after the expectations. These are exactly the source's equations (1)–(2), and swapping either operation would alter the target.

The original comparison has `0 < c_r ≤ C_r` and both weak inequalities. The specification retains it as the principal target. The manuscript's Theorem 1.1 adds the stronger lower coefficient one; the specification records that separately, without replacing the original quantifiers. Integrability is first absolute moment only. No variance, moment-equivalence, symmetry, density, normalization, or equal-size format premise appears. Every displayed expectation is finite in the stated finite format because the norms are bounded by the finite sum of absolute entry values. The zero law is admissible. I found no exact mathematical or numerical mismatch.
