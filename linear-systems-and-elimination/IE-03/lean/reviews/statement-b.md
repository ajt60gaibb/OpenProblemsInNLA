# IE-03 independent statement review B

**APPROVE** the pre-proof statement at
`15bb480400eeb34732141e2a02f55a7c229d8564`. Reviewed on 9 November 2026 by
Codex agent `/root/ie03_statement_b`, an independent AI referee with no
implementation role. This approval binds the bytes below.

| Reviewed file | SHA-256 |
| --- | --- |
| `NLA/IE03/Definitions.lean` | `39934cbfb2bba5eb0b24d3a7d45e8b8123649bbe3467685253240d2f76ad42e8` |
| `Challenge.lean` | `437e360d1c1111a6e39f30048915e1a2f99ac7331f68df2167734eee2d204c00` |
| `NUMERICAL_TARGETS.md` | `6f0d06280a66f2870c2a0475058f466f68feef1ed9b38d26b3060223a1dd3f46` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lakefile.toml` | `a36d5bdf97d0078a13cefa7767e95de7a293139452b96c4613843f680507531b` |
| `lake-manifest.json` | `358d7900d88ecc1f14f657c0edd1ef95f05a99056fdc892c83f2f24940da982d` |
| `comparator.json` | `57dc1f8dc1d60862eef53d0dc214b77948fef8714c101365c5411ca698bba5fd` |

I read the full canonical target and Andia's complete submitted manuscript
at `3017ea813328900a812c0c105ca16ad6f694857e`. I also read the accompanying
construction verifier and independently checked all three hashes against
`NUMERICAL_TARGETS.md`.

| Published source | SHA-256 |
| --- | --- |
| `linear-systems-and-elimination/IE-03/README.md` | `370f171c362ab381d996b3dd23ec7cc420638a5f82f91a520f6ef7fc0f5a7c57` |
| `references/andia-ie03-2026-10-31/main.tex` | `014ee5727ce8794d3b32d237bb393a24569201f2f2376e9a2878c99e2b9da698` |
| `references/andia-ie03-2026-10-31/verify_construction.py` | `f9cd356dbfdb0505737d24155be86eb09d47a8ccfdb7d1808b31ca1e3c27a5b1` |

## Statement correspondence

- **Input and arithmetic.** `IsHadamard n A` uses real entries and separately
  imposes the sign condition and the row Gram identity on all indices below
  `n`. The `Finset.range n` sum is the dot product of rows `i` and `j` and its
  right-hand side is the corresponding entry of $`nI`$. At positive order this
  identity implies invertibility of the square matrix. The generic field
  parameter of the Schur and pivot definitions is instantiated with
  Mathlib's real field and linear order in both exports.
- **Active step and ties.** The formula in `schur` is
  $`A_{uv}-A_{uc}A_{rv}/A_{rc}`$, with `skip` taking the increasing enumeration
  of the rows and columns surviving the chosen pivot. If `r < n+1` and
  `i < n`, `skip r i` stays below `n+1` and differs from `r`. Thus no padding
  entries enter any active update. `IsPivot` requires in-range indices, a
  nonzero divisor and weak absolute-value inequalities against the whole
  active square. Every tied maximizer is admissible. A positive-dimensional
  nonsingular active matrix has positive maximum magnitude. The scalar
  Schur complement after any such pivot is nonsingular by the block
  elimination identity. The nonzero requirement therefore agrees with the
  original exact-arithmetic problem.
- **Path coverage.** Deleting a chosen row and column in increasing order
  gives the same active entries as moving the pivot to the leading position
  and eliminating, up to permutations of the survivors. The entrywise
  update commutes with these reindexings and the next pair can be anywhere
  in the active square. Recursively this represents every admissible
  tie choice and permits the submitted paper's fixed permutation to be
  expressed by successive choices in the unpermuted matrix. `PivotPrefix`
  starts each nonempty constructor with one legal pivot and passes that
  particular Schur complement to the tail. `CompletePath` forces the order to
  reach zero, so a proof from order `n` accounts for exactly `n` pivots. The
  existential terminal function has no active entries at that order.
- **Growth and quantifiers.** The selected pivot attains the largest
  magnitude at its step by `IsPivot`. The inductive `max` with empty value
  zero gives the maximum over the positive-sized active matrices, since
  every pivot magnitude is nonnegative. The original sign matrix has
  maximum entry magnitude one at positive order, so this maximum equals the
  normalized growth factor. Quantifying `g` over every realized
  `CompletePath n A g` is sufficient for the all-paths equality even if
  distinct paths share a growth value. `cryer_false` negates that entire
  universal equality over positive orders and existing real Hadamard
  matrices. `counterexample` requires one real matrix satisfying the Gram
  and sign properties and a full path with exact growth 4608 at order 4096.
  Since 4608 differs from 4096, it suffices for the negation.

I inspected the pinned Mathlib checkout at
`0df444a360eaa60ab8c11dca51a86af692955474`. In
`Mathlib/Data/Real/Basic.lean`, `ℝ` is the Cauchy completion of the rationals
with its real field and linear-order instances. The additive absolute value
from `Mathlib/Algebra/Order/Group/Unbundled/Abs.lean` is the supremum of an
entry and its negative. The big-operator notation in
`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean` expands to the ordinary
`Finset.sum`. The bound on its summation index follows from
`Finset.mem_range` in `Mathlib/Data/Finset/Range.lean`.

## Witness scope and checks

Andia's Section 2 gives a complete-pivoting path by extending the order-16
construction through four order-four lifts. Each lift consists of two
order-two lifts. At a legal pivot of value $`p`$, the lifted first two pivots
have values $`p`$ and $`-2p`$. After the first pivot, the bound on all active
entries is $`|p|+|p|^2/|p|=2|p|`$, attained by the second pivot. Eliminating
the full $`pW_2`$ block leaves the original scalar Schur complement tensored
with $`W_2`$. These facts explain the required algebraic bridge and the
doubling of the peak pivot magnitude.

The directly checked stages go from active orders 16, 24, 32, 40 and 48 to
6, 8, 10, 12 and 0. Their pivot counts sum to 124. With the fourfold lifts
inserted the root prefix lengths are 10, 56, 246, 1012 and 4096. The final
fourteen magnitudes in the manuscript attain $`1024\cdot 9/2=4608`$, and
the source verifier checks the earlier maximum is 1024.
`NUMERICAL_TARGETS.md` correctly requires every local active entry
comparison and Schur transition, correctness of each lift, and the sign and
Gram properties of the full witness. The exports settle IE-03 through the
exact growth and the resulting negation. Their scope leaves the specified
overshoot index, the larger-order corollary and the asymptotic conjecture as
separate assertions.

I checked `verification/STATEMENT-SHA256SUMS`, inspected the retained
`verification/statement-build.log`, and independently ran
`lake env lean Challenge.lean` with Lean 4.33.1
(`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`) on arm64 macOS. It exited zero
with the two expected challenge placeholder warnings. A separate run of
the pinned `verify_construction.py` exited zero, checked all 16,777,216
supplied matrix entries and reported growth 4608. Its signed pivot sequence
digest was `a761528e59bee03cd387a0b6b50e3d44efce44fc5d734fe8a326b684f9bfbec0`.

This report covers the statement phase. The rational reproduction is
independent corroboration of the source construction. Final proof fidelity,
kernel checking of the solution, axiom auditing and Comparator remain
separate review and verification gates.
