# MF-12 independent six-module source review

**Approve the mathematical source of these nine additional exports.** I found
no blocking mathematical, scope or definition-fidelity defect in RootLimit,
Gaps, PowerBounds, Upper, JordanEntries and GapBounds. This is source-only
approval of the exact held files, not complete MF-12 verification or successful
execution of their LeanCert, kernel or Comparator checks.

Reviewer: OpenAI Codex agent `/root/next_elimination`, independent of proof
implementation author `/root/next_matrix_functions`. `CHECKS.json` binds all
six modules, their 723 lines, the unchanged frozen Definitions and 28 Challenge
statements, and the numerical statement document. `source/` retains the exact
reviewed files. Their hashes match the author's closed batch7 handoff. All nine
exported type signatures match the frozen Challenge after whitespace
normalization, with exactly one declaration per export in these six files.
Each has a LeanCert kernel-trust assertion and an axiom-print command. These
commands have not been executed or accepted by this source review.

I read the full canonical README and authored manuscript at upstream
`8f04b905eb2e0827b6b84f37d9d080ae1f05b202`; their retained copies are checked
against actual Git contents. I also reread the frozen definitions and complete
numerical obligations. All seven imported project proof modules match the
exact hashes covered by my earlier seven-module review and its run35029609317
repair addendum. Those earlier reports retain their own limited source and
actual-execution distinctions. No earlier review is silently upgraded here.

## Actual roots of polynomial growth

RootLimit proves the real limit of the specified sequence, using Mathlib's
actual `x^(1/x)` limit, continuity of real powers at one and at a positive
constant, and the product limit. The two rearrangements of real exponents
apply to nonnegative natural-number casts. In particular the auxiliary model
identity is valid at n=0 as well; eventual n>=1 is used for the final squeeze,
so no value at zero manufactures the limit. Positive c and C and the assumed
lower comparison ensure the sequence is nonnegative where monotonicity of the
nth root is used. The final exported hypothesis still quantifies over every
positive integer n. Its unused nonnegative-gamma hypothesis is harmless:
the auxiliary limit holds for every fixed real exponent, which is stronger
than needed. No joint-spectral-radius value is inserted into a definition.

I inspected the pinned Mathlib statements for real-power multiplicativity,
continuity, the root limit and natural-cast composition. The corrected global
`_root_.tendsto_rpow_div` name agrees with the pinned source. Whether every
elaboration detail succeeds remains an actual Linux gate.

## All chronological words and exact lower-word length

Gaps preserves the original convention that later chronological factors
multiply on the left. Its induction represents every binary word by a nonempty
list of nonnegative gaps. The empty word is represented by [0], leading and
trailing resets give zero endpoint gaps, and adjacent resets give zero middle
gaps. The exact identity `sum gaps + (number of gaps - 1) = word length`
therefore holds without a hidden restriction on switching patterns.

The reset factorization is proved from actual matrix products and P=VU. The
middle compressed product has the required reversed order, including a single
reset with an empty middle list. Multiplication is associated through the
rectangular U,V matrices; the factorization does not replace the original
six-dimensional program with a newly defined recurrence.

For the prescribed lower word, the natural division count and subtraction
remainder prove exact length n. Repeating the chronological block A^q then P
produces `(P*A^q)^k`, followed on the left by the remainder power A^r. The
small-length branch is exactly A^n, and the exported identity holds for every
natural n, including zero. This is a complete word-identity bridge, while the
corresponding every-length lower norm estimate remains an excluded obligation.

## Uniform powers and the upper bound for every word

PowerBounds obtains `q*u^q <= 1/(1-u)` for every q and 0<u<1 from the exact
Bernoulli denominator inequality. The denominator and 1-u are positive before
cross multiplication; discarding the additional nonnegative u^q term gives
the requested bound. The q=0 boundary is included. The exact block-power
formula then bounds all 36 entries of A^q by H=(1-mu)^(-1). Unit diagonal
entries, zero entries, both scalar powers and both Jordan off-diagonal powers
are handled explicitly. There is no finite-power extrapolation.

Upper uses ordinary finite-sum absolute-value bounds for rectangular matrix
multiplication. The successive inner dimensions are 6, 2, 2 and 6, giving
an entry bound of 144*H^2*E for `A^r V B U A^s`. The genuine six-dimensional
Euclidean operator-norm comparison introduces one further factor 6, hence
864*H^2*E. Combining the arbitrary-gap budget with
`1 + n^alpha <= 2*n^alpha` for n>=1 yields exactly 1728*H^2*n^alpha.
The no-reset word A^n is separately included using H>=1. The decomposition
also covers repeated resets and every zero gap. Thus the exported bound is
for every positive-length word in the original family, not merely the lower
construction or a collection of sample patterns. The deliberately enlarged
constant is exactly the previously approved numerical statement; no claim of
the source's sharper constant is introduced.

## Natural logarithmic gap and actual Jordan products

GapBounds uses Mathlib's exact natural logarithm, with q=floor(log_4 n), for
all n>=4. It derives q>=1, k>=1, 4^q<=n<4^(q+1), the short-block inequality
and the exact remainder identity. From natural division,
`n < (k+1)*(q+1) <= 4*k*q`; combining this with 4^q<=n gives
`k*q/4^q >= 1/4`. Casting occurs only after the integer estimates, and the
power denominator is strictly positive. This proves the actual chosen-gap
loss mass for every n>=4, without a floating logarithm, approximate floor,
or subsequence restriction.

JordanEntries derives the entry formula for `(I+N)^n` by actual right matrix
multiplication. Multiplication by the upper shift selects the previous column;
column zero is handled separately. The induction uses Pascal's rule and the
correct below-diagonal, on-diagonal and above-diagonal cases, including n=0
and the one-dimensional case m=0. Consequently each diagonal entry remains
one, so the Jordan generator is nonzero.

For the pair {J,0}, any word containing the zero generator has zero product,
while the all-J word gives J^n. The previously reviewed finite-maximum bridge
then proves the exact growth equality, including arbitrary words. No
nonzero-word restriction is hidden in the family supremum. The all-m/all-n
Jordan norm bounds are separate remaining obligations and are not claimed
from the entry formula alone.

## Trust, scope and attribution

The nine exports are listed in `CHECKS.json`. Together with the prior
fourteen-export source review they cover mathematical source for 23 of the
28 frozen declarations. The five excluded declarations are
`fractional_lower_all_lengths`, `fractional_growth_estimates`,
`jordan_growth_estimates`, `fractional_tensor_growth`, and
`realizes_every_nonnegative_exponent`. The last is the complete original
all-real-exponent target. This review does not establish any of these five,
count MF-12 as complete, or increment a verified-problem total.

The inspected implementation uses exact symbolic identities, finite sums,
monotone estimates and standard limits; it requires no numerical interval
subdivision or exhaustive word computation. A source lexical check found no
new axiom, hole, native proof, unsafe code, custom implementation replacement,
or Challenge import in the six files. This is not a substitute for a
transitive axiom audit. No Lean/Lake/build command was run locally, and no
mechanical acceptance of these six exact files is asserted.

Original mathematics remains Matthew J. Colbrook, University of Cambridge
DAMTP. The formalization credits George Stepaniants, Department of Computing
and Mathematical Sciences, California Institute of Technology, Pasadena,
California, USA, and discloses AI assistance. No George email is present.
The review applies the repository's scoped Tau Ceti correctness, fidelity,
generality, reuse, computational economy, API and attribution criteria. It is
not official Tau Ceti certification or external human peer review. Actual
Linux source-matched acceptance, the complete dependency graph, Comparator,
default-kernel replay, rejection controls and two final independent referees
remain necessary before complete publication acceptance.
