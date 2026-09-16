# MF-12 independent seven-module proof-prefix review

**Approve the mathematical source of this fourteen-export prefix.** No blocking
mathematical, definition-fidelity or scope defect was found in the seven reviewed
modules. This is independent source-only approval, not successful Lean
elaboration, complete MF-12 verification, Comparator/default-kernel acceptance,
or approval of the remaining fourteen exports.

Reviewer: `/root/next_elimination`, independent of implementation author
`/root/next_matrix_functions`. The exact reviewed modules are Words, Parameters,
Norms, Tensor, MatrixAlgebra, Budgets and HolderBound. All seven, the frozen
Definitions and the independent Challenge match actual immutable Git contents
at `f3c22761166868df60938a27bdb08111dfc90f0d`. `CHECKS.json` records their Git paths,
blobs and SHA-256 hashes; `inputs/` retains the exact files. MatrixAlgebra's
original batch hash 0d206493… changed to d22e583b… only by removal of one trailing
empty line. Both exact versions are retained and the whitespace-only change is
verified in `WHITESPACE-ADJUSTMENT.json`. RootLimit is deliberately excluded.

I read the entire seven-module implementation, the frozen boundary, the original
canonical README and complete authored manuscript at upstream
`8f04b905eb2e0827b6b84f37d9d080ae1f05b202`. The canonical sources are copied and
independently bound to their Git blobs. Fourteen literal exported type signatures
match the frozen Challenge after whitespace normalization. Each is implemented
once and has LeanCert kernel-trust and axiom-print commands. There are no new
axioms, proof holes, native proofs or Challenge imports in these modules. No
Lean/Lake command was run by this referee; the existence of diagnostic commands
is not evidence that they have executed successfully.

## Genuine word maxima and operator norms

Words correctly preserves chronological multiplication: later list elements
act on the left. The append and cons identities, binary encoding and repeated
single-letter products follow that order. The finiteness proof enumerates all
length-n lists from the finite subtype of generators, not merely selected
switching patterns. Nonemptiness comes from an actual repeated generator;
finite nonempty supremum attainment produces a genuine maximizing word.
The binary bridge does not require A and P to be distinct and covers every
word in their pair family. Hence no arbitrary value of a default supremum is
used to manufacture a growth statement, including at length zero.

Norms uses the actual Euclidean continuous linear map from the frozen definition.
A coordinate unit vector proves every absolute matrix entry is at most its
operator norm. The reverse inequality follows from Cauchy–Schwarz in each row
and a second finite sum over rows, giving exactly `dimension * entryMax`.
Both squared quantities are nonnegative before passing from squared bounds to
norm bounds. Positive-dimensional maximum attainment handles the added-zero
case explicitly, choosing a genuine matrix entry when the maximum is zero.
No ambient sup norm is silently substituted for the spectral norm.

Tensor is the actual Kronecker matrix reindexed by the specified finite-product
equivalence. It proves the multiplication and identity laws and then the complete
all-word tensor identity. The product of attained entry maxima is attained in
the Kronecker matrix; the reverse entry bound uses absolute multiplicativity.
Combining this identity with the two operator-norm comparisons gives the exact
coarse factors d*e in both requested inequalities. Positivity of both dimensions
justifies the lower-bound division. These are valid fixed constants for the
later polynomial-growth construction and require no unproved exact tensor
spectral-norm formula.

## Exact matrices, parameters and all powers

Parameters retains lambda=1/4 and mu=lambda^(1−alpha), with the complete
0<alpha<1 range. The proof establishes lambda<mu<1, finite positive reciprocal
power bound, and positive ordered lower/upper constants. The scalar induction
for loss=q*4^(−q) includes q=0 and separates q=1 before using the q≥1 induction
estimate. Its upper bound is 1/4. The gain/loss identity is derived with real
power rules under explicit nonnegativity and positive complementary exponents;
zero gaps are included and no zero-power ambiguity is used as an exclusion.

MatrixAlgebra retains the literal original 6-by-6 source arrays and rectangular
U,V. Actual matrix multiplication gives UV=I, then P squared=P. The (0,1) entry
proves A differs from P for every alpha, regardless of mu. The Jordan formula
holds for every real t and every natural power, including t=0 and exponent zero.
The explicit block power form is proved by an initial identity and a symbolic
successor multiplication. Every finite scalar `change` is applied to an actual
matrix-entry goal, so the final compressed identity is a bridge from U*A^q*V,
not a newly defined recurrence standing in for that matrix product. The sparse
entries and signs agree with the original manuscript and frozen source arrays.

The additional Bernoulli denominator bound is proved for every natural k and
all 0≤ell<1. Its induction multiplies by a nonnegative power; the denominator
1+k*ell is strictly positive. If k*ell≥1/4, the reciprocal is at most 4/5,
so the lost mass is at least 1/5. This safely replaces the source's sharper
exponential constant without numerical evaluation. The k=0 and ell=0 boundary
cases remain valid.

## Arbitrary-gap budget and Holder estimate

Budgets follows the reversed chronological order exactly: each earlier gain
is multiplied by the product of later diagonal factors. The cons recurrences
therefore have the correct orientation. Diagonal and tail weights lie in [0,1]
for every list, not only positive gaps. The exact telescoping sum is
`1 − product(1−loss)`, including the empty list. Induction through actual
compressed-matrix multiplication gives the full diagonal and off-diagonal
formula; all zero gaps and repeated resets are retained.

HolderBound uses Mathlib's finite real Holder inequality with conjugate
exponents 1/alpha and 1/(1−alpha). I checked the pinned conjugate-exponent and
finite-Holder API statements against this use. It applies to nonnegative
`f_i=q_i*w_i` and `g_i=loss_i*w_i`; the exact gain identity and real-power
multiplicativity make each product of fractional powers equal gain_i*w_i.
The sum of f is at most the total gap length, while telescoping bounds the sum
of g by one. Monotonicity of the real powers then gives the requested bound
on the actual off-diagonal budget. Empty lists and zero terms satisfy the
same identities, so there is no hidden nonempty or nonzero-gap premise.

## Scope, efficiency and remaining work

The fourteen reviewed declarations are listed exactly in `CHECKS.json`; all
remaining fourteen are also listed there as excluded. In particular this
prefix does not yet prove the all-word upper bound for the original 6-dimensional
family, the full gap factorization, logarithmic lower word and every-length
lower bound, the positive-eigenvalue Jordan estimates, every-real-exponent
assembly, or the actual nth-root limit. The canonical target requires all of
those bridges. These useful intermediate proofs are not a complete solution
by themselves, and no problem count should increase from this prefix verdict.

The proof design uses symbolic induction, finite attainment, ordinary norm
inequalities and exact real Holder bounds. It introduces no interval
subdivision, large word enumeration or sampled certificate as a premise.
Original mathematics remains Matthew J. Colbrook, University of Cambridge
DAMTP. George Stepaniants's formalization credit includes the Department of
Computing and Mathematical Sciences, California Institute of Technology; no
George email is published in the proof sources.

This is scoped Tau Ceti-style review of correctness, full-boundary fidelity,
source reuse, computational economy and clarity, not official certification
or external human review. Actual Linux diagnostics may require elaboration
repairs. Later source changes need a byte-bound addendum; full publication
acceptance additionally requires the complete source-matched build, LeanCert
and standard transitive-axiom results, actual default-kernel and Comparator
replay with rejection controls, and two independent final referees.
