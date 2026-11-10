# IE-03 independent statement review A

**Phase:** Pre-proof statement review  
**Reviewer:** Codex sub-agent `ie03_statement_a` (AI agent and nonauthor)  
**Date:** 2026-11-09  
**Verdict:** APPROVE the exact statement at `15bb480400eeb34732141e2a02f55a7c229d8564`.

I inspected the complete canonical problem, the submitted manuscript including
Theorem 1 and its proof, the construction verifier, the numerical specification,
the concrete Lean definitions, and both Challenge signatures. The published
source is `3017ea813328900a812c0c105ca16ad6f694857e`.

| Input | SHA-256 |
| --- | --- |
| `linear-systems-and-elimination/IE-03/README.md` | `370f171c362ab381d996b3dd23ec7cc420638a5f82f91a520f6ef7fc0f5a7c57` |
| `references/andia-ie03-2026-10-31/main.tex` | `014ee5727ce8794d3b32d237bb393a24569201f2f2376e9a2878c99e2b9da698` |
| `references/andia-ie03-2026-10-31/verify_construction.py` | `f9cd356dbfdb0505737d24155be86eb09d47a8ccfdb7d1808b31ca1e3c27a5b1` |
| `NLA/IE03/Definitions.lean` | `39934cbfb2bba5eb0b24d3a7d45e8b8123649bbe3467685253240d2f76ad42e8` |
| `Challenge.lean` | `437e360d1c1111a6e39f30048915e1a2f99ac7331f68df2167734eee2d204c00` |
| `NUMERICAL_TARGETS.md` | `6f0d06280a66f2870c2a0475058f466f68feef1ed9b38d26b3060223a1dd3f46` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lakefile.toml` | `a36d5bdf97d0078a13cefa7767e95de7a293139452b96c4613843f680507531b` |
| `lake-manifest.json` | `358d7900d88ecc1f14f657c0edd1ef95f05a99056fdc892c83f2f24940da982d` |
| `comparator.json` | `57dc1f8dc1d60862eef53d0dc214b77948fef8714c101365c5411ca698bba5fd` |
| `verification/STATEMENT-SHA256SUMS` | `0e329ddbf8a7376e369a0a00a5ea8a802a16cc271b3f676fec9425d812031f0f` |
| `verification/statement-build.log` | `7d464e9cd6334ed651f91fd444b21b1e13fbc5484ff9310d5b5939083e25c326` |

I confirmed the Mathlib checkout was clean at
`0df444a360eaa60ab8c11dca51a86af692955474`. I checked its ordered real field
and division in `Mathlib/Data/Real/Basic.lean`
(`b1dde0e82be30e8a9ca87b23c46d04afc92be61818622ba6d4603daa4d4a9f70`),
the additive absolute value and its notation in
`Mathlib/Algebra/Order/Group/Unbundled/Abs.lean`
(`7991bf23c32cc89e3a8f5cf0f054ddf49e84aa8326cbf5609e4addd70d8091da`),
and the finite range and sum in `Mathlib/Data/Finset/Range.lean`
(`6278700253a11cbbf7c17a8ff8877ec6b529e09889d234669dd5fe4f43735e7e`)
and `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`
(`2f39541f66288cb9ae9f77d97fd3656825a1dd1a4b5ca6a156f938d8fa1678a8`).
The finite sum ranges over exactly the column indices below the matrix order.
I ran `shasum -a 256 -c verification/STATEMENT-SHA256SUMS` and
`lake env lean Challenge.lean` using Lean 4.33.1 at
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. Both exited zero. The Lean output
contained the two expected Challenge placeholder warnings and agreed with the
retained type-check log.

## Target correspondence

- **Field and Hadamard assumption.** The public theorems use Mathlib's exact
  ordered field `ℝ`. On the active square, `IsHadamard` requires each entry to
  be exactly `1` or `-1`. For rows `i,j` its sum is the `(i,j)` entry of
  `A Aᵀ`, with right side `n` on the diagonal and zero elsewhere. At
  positive order this identity gives the square matrix a right inverse
  `Aᵀ/n` and hence nonsingularity.
- **Pivot and Schur semantics.** In order `n + 1`, for each chosen index
  `r < n + 1`, `skip r` sends `0,...,n-1` in increasing order onto the
  old indices other than `r`. The column map does the same for `c`.
  After bringing `(r,c)` to the first row and column, the remaining entry is
  the old survivor entry minus the column factor times the row factor
  divided by `A r c`. This is exactly `schur` at each survivor pair.
  `IsPivot` checks both indices, a nonzero denominator, and the absolute
  value comparison at every pair in the active square. Its weak inequality
  permits any maximizing tie. Any intermediate ordering of survivors can be
  transported to their increasing order by relabeling the next chosen row and
  column. The update transports entrywise, so the path's growth is preserved.
  Out-of-range entries of the total functions are irrelevant.
- **Full path and growth.** A `PivotPrefix.step` certifies a legal choice and
  lowers the active order by one. The `empty` constructor retains the current
  order. Requiring final order zero in `CompletePath` therefore certifies
  exactly `n` pivots. The terminal matrix has no active entries. Every chosen
  pivot magnitude equals its active maximum, so the maximum recurrence
  computes the maximum over the nonempty active Schur complements. Its zero
  base leaves the maximum of nonnegative magnitudes unchanged. The positive
  Hadamard input has initial maximum one, giving the exact normalization of
  the canonical growth factor.
- **Quantification.** For each positive order and real Hadamard matrix, the
  unnegated statement of `cryer_false` quantifies over each real `g`
  realized by some complete path. Since the required equality depends only
  on that value, this is equivalent to quantifying over every admissible path.
  The signature therefore negates the original universal assertion.
- **Witness and scope.** `counterexample` requires the same real order-4096
  matrix to satisfy the full sign and Gram conditions and admit a complete
  path of growth exactly 4608. This suffices for the claimed negative
  resolution because `4608 > 4096`. The manuscript supplies a construction
  from the Sylvester matrix, using a lifting lemma for the order-two factor
  twice per order-four lift. The five directly checked pivot counts
  `10,16,22,28,48` sum to `124`. With each preceding prefix multiplied
  by four, their cumulative counts are `10,56,246,1012,4096`.
  The submitted local verifier uses whole-active comparisons and rational
  Schur updates on those local choices. It does not supply hypotheses to
  either Lean signature. A formal proof must establish the finite comparisons
  and updates, the lifting identity, and the sign and Gram conditions
  internally. The exact overshoot position and extension to larger orders
  are supplementary manuscript results outside these signatures.

This approves statement fidelity and scope for the listed bytes. I did not
verify a Lean proof body, reproduce the submitted computation, audit transitive
axioms, or run Comparator in this phase.
