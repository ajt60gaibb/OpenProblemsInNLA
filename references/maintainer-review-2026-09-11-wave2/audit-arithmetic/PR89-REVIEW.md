# Independent review of PR #89

Reviewed head: `3443179cb62b410678f3c67f26cd8df56ba6133a`.
Published comparison base: `16369809e6e600144bd350ab70b7473b652f46f1`.
Review date: 2026-09-11. Frozen snapshot: `../pr-89`.

**Verdict: PASS for the submitted scope. No mathematical or certificate blocker found.**
AA-01 is solved in its explicitly stated constant-free finite-tree model.
AC-11 is established through order 35 and AC-12 through order 10; neither
all-orders problem is solved. This is an independent AI-agent mathematical/code
audit and exact computation, not formal proof-assistant certification or
external human peer review. Existing submitted review labels were not evidence.
No novelty or priority claim is assessed or endorsed.

## Identity and provenance

`identity-checks.json` records that the entire `problem_ids.json` is byte-identical
to the published base. For AA-01, AC-11 and AC-12, everything from the original
`## Problem statement` through the end of each canonical README is byte-identical
to that base. Only metadata and a new preceding resolution section change. The
canonical paths and mathematical targets are preserved, including negative
diagonal entries being allowed in AC-12 and below-diagonal entries being +1.

AA-01 overlaps pending PR #68 at the same permanent catalog entry. It must not
receive a second ID, and the two manuscripts' authorship and provenance should
remain separate. The arithmetic submission explicitly discloses that the
historical AA-01 experimental programs are absent, with only two logs retained.
The complete final proof is reviewable; those missing programs, claimed run
counts and historical compiler/solver budgets were **not** independently rerun
or certified. The canonical page and final manuscript already state this limit.

## AA-01 proof audit

Read the complete final `manuscripts/AA-01.tex`, including all lemmas, corollaries,
face criterion, examples, model boundaries and reproducibility discussion. The
theorem matches the canonical target: integer polynomial p with p(0)=0, n>=1,
exact input reals, finite computation trees, rounded +,-,*, exact negation and
comparison of available values, and reuse of stored results. Independent errors
belong to operation occurrences; comparing or reusing a stored value introduces
no new error. Arbitrary real constants and unbounded loops are excluded.

For every signed ordered-gap chart x=L y, y>=0, let q=p composed with L and
q# be the collected coefficient absolute-value polynomial. The proposed
necessary and sufficient criterion is q#(y)<=C|q(y)| for some finite C>=1 in
each chart. All 2^n n! charts are finite and their constants can be maximized.

Sufficiency in lines 149-200 is sound. Signs and order are obtained from exact
comparisons of raw inputs and their exact negatives. Each gap is a single
subtraction of original magnitudes. Integer coefficients can be implemented by
repeated addition because every nonzero monomial has positive degree. Unrolling
the arithmetic only for error analysis retains multiplicities of shared error
factors. If R bounds those factors, (1+u)^R-1<=2Ru for Ru<=1/2, giving error at
most 2Ru q#. Choosing u<=eta/(2CR) proves uniform relative accuracy, including
exactness at zeros. The zero polynomial is computed by self-subtraction.

Necessity in lines 235-477 survives the difficult branch and alias cases.
Set M=n+N(P), gamma=u/(64M), epsilon=u^2/(1024M), u<=1/4. At each new rounded
root, a multiplier in [1-u/2,1+u/2] can avoid both signs of every preceding root:
the total forbidden interval length is at most 12M gamma=3u/16<u. Reusing a root
does not invoke this choice again. Zero pre-results are kept zero.

Within a chart every raw input and pairwise raw sum/difference is, up to sign,
a nonnegative gap combination. Multiplicative gap perturbations by factors
1+-epsilon thus preserve relative size, sign, and exact zeros. Replay fixes all
previous rounded roots. Raw/raw comparisons use this primitive-form property;
mixed comparisons use separation; rounded/rounded comparisons are unchanged.
The pre-result perturbation bounds for sums and products are at most
epsilon/gamma=u/16. Restoring each rounded result needs multiplier error at most
9u/(16-u)<=4u/7<u. The output can be rounded, raw, or zero, and all three cases
are covered. There is no assumption that setting errors to zero on a rounded
execution path leaves its branch choices valid.

Accuracy at tolerance 1/4 then gives |p(L diag(t)y)|<=2|p(Ly)| on one fixed
relative box, without dividing by p(Ly). Tensor-product Vandermonde interpolation
bounds the coefficient l1 norm of Q_y(t)=p(L diag(t)y) by a fixed multiple of its
supremum on that box. Its coefficient norm is precisely q#(y), proving necessity
uniformly even on chart boundaries and at polynomial zeros.

The criterion is an integer-coefficient first-order sentence over the reals;
squaring is valid because q# and C are nonnegative. Complete real quantifier
elimination terminates, and subsequently testing integer C=1,2,... terminates
when domination holds. This uses established effective real QE, not the
completeness of a timeout-limited experimental solver. A primary corroboration
of complete multivariate real QE is [Kosaian, Tan and Platzer](https://arxiv.org/abs/2209.10978v2).
The older model-dependent accurate-evaluation context is correctly distinguished
from this specific theorem; see [Demmel, Dumitriu and Holtz](https://arxiv.org/abs/math/0508350v2).

The face criterion in lines 506-610 is also valid. An exposed-face positive zero
gives a monomial scaling ray on which |q|/q# tends to zero. Conversely, pass to
a limit of normalized absolute coefficient weights. Its nonempty support T has
a convergent logarithmic component in the span of exponent differences in T;
every point outside T tends strictly below it in the orthogonal component. One
sufficiently late such component exposes exactly T as a face, and the limiting
signed-weight cancellation supplies its positive zero. This includes the whole
face; the identically zero polynomial is treated separately. The finite
existential obstruction encoding requires strict separation of excluded points.
The isolated-zero and Motzkin examples check algebraically. Parent reviewer
independently recomputed 442 charts/14,918 primitive forms, 48 Motzkin charts
(16 SOS identities), and the isolated-zero asymptotic example; see
`root-mathematical-review.md`, `root_independent.py`, and its JSON output.

## AC-11/AC-12 analytic and implementation audit

Read the complete final `manuscripts/AC-11-12.tex`, the full verifier and range
checker, their included `spectrum.cpp`, the Python DP/parser/tests, the discovery
programs, and table/realization scripts before executing needed checks.

The universal divisor follows by expanding A=J-2D into rook numbers:
per(A)=sum_k (-2)^k (n-k)! r_k(D). Each coefficient has valuation
n-s2(n-k)>=n-floor(log2(n+1)). Thus the positive permanent of any sign matrix is
at least q(n)=2^(n-floor(log2(n+1))). A complete sign matrix with permanent q(n)
establishes the finite minimum; a cofactor dot product by itself does not.

The polarization formula is exact by summing signed monomials: nonzero terms
must use every row an odd number of times, and total degree forces each once.
Fixing the first sign halves the sum. For an even number of sign rows, halved
column sums are integers and the formula computes half the permanent. In odd
orders the first-row expansion uses a weighted elementary symmetric derivative.
The recurrence Q_new=Q*t_j+b_j*P, P_new=P*t_j uses old P and handles zero column
sums without division. Transposing the input in the verifier preserves permanent.

In `verify_permanent.cpp`, Gray-code chunk initialization and the transition
`1+ctz(step)` visit every sign state exactly once; Gray-code parity equals the
step parity used for signs. Zero skipping is valid for both the even product
and the odd derivative. Unsigned 128-bit wrap is deliberate modular arithmetic.
The Mersenne reduction for 2^61-1 is exact; the multiplier bound is at most 20
for accepted n<=40, so one final subtraction suffices. The two residues have
coprime moduli. A separate arbitrary-integer check verifies
2^128(2^61-1)>n!/2+|claimed permanent|/2. Hence matching residues imply equality
of integers, not just a probabilistic modular check. Negative claims, dimensions,
sign entries, parity, missing data and trailing data are checked.

In `check_range.cpp`/`spectrum.cpp`, row/column sign normalization preserves the
absolute permanent. Every orbit has a lexicographically least core. Its sorted
rows/columns give the allowed prefix-block transitions. Moving a later row into
an earlier position and sorting within the then-identical column blocks proves
the additional orderly tests necessary; uniqueness of representatives is not
needed. The reversed bit ordering in the code agrees with the manuscript's
low-bit prefix-of-ones convention.

The prefix bound is (n-k)! sum_|I|=k |per(prefix[:,I])|. Divisibility allows
pruning only when every multiple of q(n) up to this bound belongs to the verified
catalog. The contiguous progression stops at any gap and disables pruning when
zero is absent. Unpruned leaves are checked exactly. At n<=10 all integer minor
updates and completion bounds are bounded by n!<=3,628,800, well inside the
chosen types. The bitsets cover all 512 possible core rows at n=10.

Finally, restricted witness membership and unrestricted inclusion are separate
obligations. All below-diagonal witness entries are checked to be +1. Both signed
ranges follow from absolute ranges because negating the first row preserves U_n.
The primary source's all-orders minimum/range questions remain distinct from
these finite results: [Ingram and Razborov](https://arxiv.org/html/2507.09433v1).

## Fresh exact executions

Only independently rebuilt inspected verification binaries were trusted. Boost
1.88 headers came from its official release archive with SHA256
`46d9d2c06637b219270877c9e16155cbd015b6dc84349af064c088e9b5b12f7b`.
No submission generator or long heuristic discovery search was needed.

| Check | Result |
|---|---|
| Every complete `min1` through `min35` matrix, four verifier threads | All 35 PASS; q(35)=1,073,741,824 |
| Exhaustive range inclusion, every n=1,...,10 | All PASS, zero uncovered values |
| Order 9 coverage | 22,406,026 nodes; 21,199,177 certified branches; 447,415 explicit leaves |
| Order 10 coverage | 708,191,216 nodes; 685,898,772 certified branches; 8,776,490 explicit leaves |
| All submitted spectral witnesses, arbitrary-integer subset DP | All 5,528 PASS |
| All same witnesses, fresh independent Ryser inclusion-exclusion | All 5,528 PASS |
| Fresh exhaustive unpruned normalized matrices, n=1,...,5 | 1+2+16+512+65,536 matrices; every spectrum equals catalog |
| Direct permutation validation | Every normalized matrix through n=4; fresh random/structured matrices through n=7 |
| Fresh C++ crosschecks against Ryser | 144 PASS, including 55 negative permanents |
| Fresh deliberately wrong claims | All 288 rejected |
| Fresh malformed matrix inputs | All six rejected |
| Fresh Ryser evaluation of AC-11 matrices | All n=1,...,14 PASS |
| Submitted random/negative harness | 120 cases PASS; wrong claims and malformed input rejected |
| Incomplete allowed ranges | Removing attained 4 at n=4 or 1,280 at n=8 correctly fails; malformed n=8 value 33 rejected |

The 5,528 count is 2*(1+2+2+5+8+16+36+158+506+1933)+158+36.
These are witness records across 22 catalogs, including duplicated algorithm
variants. Witness membership is not counted as evidence of range completeness;
the separately rerun exhaustive inclusion is essential at every order.

Reproduction records: `runs/full-matrix-checks.log` and JSON, `runs/range1-9.log`,
`runs/range10.log`, `runs/submitted-data-tests.log`,
`runs/independent-permanent-checks.log`, and `independent-permanent-results.json`.
Fresh independent source: `independent_permanent_checks.py` (does not import
submitted Python code); full matrix driver: `run_full_matrices.py`.

## PDF QA and final recommendation

Rendered and visually inspected all five final canonical/manuscript PDFs,
covering all 27 pages. No clipping, missing glyphs, unresolved references or
unreadable formulas were found. Rebuilt every unchanged TeX source twice with
XeLaTeX and shell escape disabled in scratch directories. All 27 pages have
identical extracted text to their submitted PDFs and no build warnings. Four
PDFs also have identical raster pixels. AA-01 canonical page 1 has a negligible
vertical-spacing difference; its source and submitted render were inspected
side by side and both are legible with identical content. Retained historical
PDFs are provenance artifacts, not the final documents used for the proof audit.
Evidence is in `pdf-qa/`, `pdf-source-rebuild-results.json`, and the two QA scripts.

The submitted head is mathematically reasonable to accept with its present
status boundaries and disclosures. Keep AA-01 at its original solved entry,
record AC-11 only through 35 and AC-12 only through 10, and retain both permanent
problem pages as partially resolved. Preserve separate AA-01 submission
provenance when integrating the overlap with PR #68. No source changes or
mathematical corrections are required by this audit.
