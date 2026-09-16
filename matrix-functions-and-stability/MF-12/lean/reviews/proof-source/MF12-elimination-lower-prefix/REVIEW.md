# MF-12 independent Jordan and fractional lower-bound review

**Approve the mathematical source of these three additional exports.** I read
all 291 lines of the held JordanBounds and Lower modules and found no blocking
mathematical or scope defect. The three declarations are
`jordan_growth_estimates`, `fractional_lower_all_lengths`, and
`fractional_growth_estimates`. Their complete literal types match the frozen
Challenge after whitespace normalization. This is independent source-only
approval, not actual Lean acceptance or complete MF-12 verification.

Reviewer: OpenAI Codex agent `/root/next_elimination`, independent of author
`/root/next_matrix_functions`. The exact two hashes supplied by the author
are retained in `CHECKS.json` and the corresponding files in `source/`.
The unchanged Definitions, numerical obligations and all 28 frozen signatures
were checked again. All thirteen earlier proof modules still match the
source versions covered by my previous prefix reviews and repair addendum.
The full canonical original target and manuscript at upstream
`8f04b905eb2e0827b6b84f37d9d080ae1f05b202` were read in the adjoining review;
its source provenance and exact hashes are repeated here.

## Jordan estimates in every dimension and at every length

The descending-factorial comparison is a valid symbolic induction. For
k<=m<=n, the factor inequality is `n*(m-k) <= m*(n-k)`, justified with the
natural subtraction identities and m*k<=n*k. Each remaining factor is
nonnegative. At k=m, the identity between a descending factorial and
`m! * choose(n,m)` gives `n^m <= m^m * choose(n,m)` after cancellation of
the strictly positive factorial. This is an exact finite algebraic inequality,
not an asymptotic binomial estimate or a numerical factorial computation.

For m>0 and n>=m, the actual top-right entry of J_m^n is choose(n,m), and
absolute-entry domination by the genuine operator norm gives the required
lower constant m^(-m). Division uses m^m>0. For n<m the proof instead uses
the unit diagonal and n^m<=m^m, so it retains every small length. The m=0
branch has a one-dimensional unit diagonal and L_0=1; it never divides by
zero. The lower helper even permits n=0 without altering the frozen theorem,
which requires all n>=1.

For the upper bound, every actual entry is either zero or choose(n,j), where
0<=j<=m. The imported exact estimate choose(n,j)<=n^j and n>=1 give the
entry bound n^m. The already reviewed operator-norm comparison multiplies by
the true dimension m+1. Thus both constants in the frozen Jordan theorem are
preserved. Nonzero J_m follows from its actual diagonal, so the later two-point
family cannot collapse to a singleton through this construction.

I checked the relevant pinned Mathlib descending-factorial, binomial and
power inequalities against their use. The proof retains integer arithmetic
until the ordered real inequality is needed; no approximate growth law is
substituted for these exact bounds.

## The actual fractional word at every positive length

Lower proves the full geometric-power identity for the actual 2-by-2 triangular
matrix, for every natural k and every nonzero loss. The zero power is the
matrix identity and the successor multiplication yields the off-diagonal
ratio formula by ordinary field algebra. The application proves positive
loss from the exact chosen gap q>=1 before division, so the zero-loss case is
not silently excluded from a target that needs it.

The reset identity is derived from P=VU and compressed=UA^qV:
`(P*A^q)^k V = V*compressed^k`. Padding on the left by A^r leaves the first
coordinate of A^r V equal to (1,0). Consequently the selected entry of the
actual six-dimensional product times V is exactly the compressed geometric
term, with the source's chronological order unchanged. This is the necessary
bridge from the compressed computation back to the prescribed original word.

The norm estimate uses the exact entry identity
`(B*V)[0,1] = B[0,4] + B[0,5]`. Each of those two entries is at most its
absolute value and hence at most the genuine Euclidean operator norm of B.
This gives the safe factor two directly, avoiding a square-root or numerical
Rayleigh-quotient calculation. The loss/gain ratio is exactly `(4^q)^alpha`;
the natural-log upper bound n<4^(q+1) therefore yields
`lambda^alpha * n^alpha <= gain/loss` for alpha>0.

The earlier exact mass bound k*loss>=1/4 and Bernoulli inequality give lost
mass at least 1/5. Its multiplier gain/loss is explicitly nonnegative.
Combining these two inequalities with the selected-entry norm comparison
produces precisely `lambda^alpha/10 * n^alpha <= norm(actual lower word)`.
The use of 1/10 is the previously approved conservative constant, not an
unrecorded change to the source's sharper constant.

For n=1,2,3, the defined word is A^n. The proof uses its actual unit diagonal
and lambda*n<=1, so the same lower constant holds. The result is therefore
at every positive integer length, including the prescribed small-length
branch, with fixed matrices and constants. It is not a subsequence claim,
a selected-matrix surrogate, or an existential choice of a different word.

Finally, `fractional_growth_estimates` passes this actual word through the
previously proved finite-family maximum bridge for the lower inequality.
The upper inequality quantifies over every binary word and invokes the
all-word bound. Both halves therefore concern the original family maximum;
no unproved supremum attainment or family/word equivalence is introduced.

## Scope and mechanical limits

These three source approvals extend the previous mathematical source reviews
to 26 of the 28 frozen exports. The remaining two,
`fractional_tensor_growth` and `realizes_every_nonnegative_exponent`, are
explicitly excluded. In particular the every-real-exponent finite-family
assembly and final complete target are not certified by this prefix review.
The dimension, constants, distinctness and actual root limit still need to
be combined in their complete statements, and actual Lean checking remains
a separate requirement throughout.

Each current export has a source LeanCert kernel assertion and axiom-print
command, but I have not inspected a successful execution for these two
modules. A lexical check found no hole, new axiom, native proof, unsafe
implementation, custom implementation replacement or Challenge import. No
local Lean/Lake/build command or finite numerical experiment was run. These
source checks are not transitive kernel or Comparator evidence. Complete
publication acceptance still needs source-bound Linux compilation, actual
standard-axiom and LeanCert results, default-kernel replay, Comparator and
negative controls, and two independent final referees.

The source preserves original mathematics credit to Matthew J. Colbrook,
University of Cambridge DAMTP, and George Stepaniants's formalization credit
with the Department of Computing and Mathematical Sciences, California
Institute of Technology, Pasadena, California, USA. It discloses AI assistance
and adds no George email. This is scoped Tau Ceti-style review of fidelity,
correctness, endpoints, reuse, computational economy and documentation, not
an official Tau Ceti verdict or external human review. No verified-problem
count should increase on the strength of this source-only report.
