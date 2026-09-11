# Additional independent mathematical review of PR #89

Reviewed source head: `3443179cb62b410678f3c67f26cd8df56ba6133a`.
Date: 2026-09-11. This review independently corroborates the analytic arguments;
the separate main PR89 report records the required full certificate reruns.
It is AI-agent mathematical review, not proof-assistant certification or
external human peer review. No novelty or priority conclusion is made.

## AA-01

I read the complete mathematical argument in the final 856-line TeX manuscript,
including the face-polynomial criterion, examples, model boundaries and the
historical software claims. The canonical target is exactly the constant-free,
finite computation-tree, whole-real-space model also considered in pending
PR #68. These submissions overlap one permanent entry; their provenance and
authorship records should remain separate, with no new ID assigned.

The separated-execution lemma correctly chooses each newly rounded root away
from both signs of every earlier root. Each forbidden interval has length less
than 6 gamma; two signs and at most M earlier roots exclude at most 3u/16 of an
interval of length u. Nonzero roots are separated even when zero-error symbolic
expressions agree. Stored aliases remain the same root, so reuse does not
incorrectly receive a new error.

Signed prefix sums make every raw input and pairwise sum/difference a signed
nonnegative combination of gaps. Multiplicative gap perturbations preserve these
forms relatively, including equality and zero gaps. In replay, two rounded roots
are held fixed; two raw roots use the primitive-form bound; a mixed sum uses
separation. Products and zero pre-results are covered. The new multiplier budget
is at most 9u/(16-u) <= 4u/7 < u for 0<u<=1/4. Thus every selected comparison,
including an equality branch, can be replayed and every rounded value preserved.
The output may be a raw signed input, but its relative change is then bounded
by epsilon, exactly as the subsequent argument allows.

Accuracy at one tolerance gives |p(L diag(t)y)| <= 2|p(Ly)| without dividing by
p(Ly); zeros are therefore included. Tensor-product interpolation on a fixed box
bounds the coefficient l1 norm uniformly. For Q_y(t), that norm is exactly the
collected gap majorant, so necessity follows without assuming that a branch
reached under rounding computes p when its errors are set to zero.

Sufficiency uses exact sign/magnitude comparisons on raw inputs and computes
each gap from two original magnitudes. Every nonzero monomial has positive
degree because p(0)=0; integer coefficients are finite repeated additions, so
no forbidden constant input is introduced. Reused errors appear with their
actual multiplicities in the unrolled products. The relative coefficient bound
2Ru controls the absolute forward error by the majorant. A finite maximum over
charts supplies uniform accuracy with a fixed tree. The zero polynomial is a
self-subtraction. The real first-order decision sentence is correctly squared
with C>=1, and the finite real-closed-field decision procedure terminates; no
useful complexity or finite-resource solver completeness is asserted.

The face criterion is also sound. A positive zero of an exposed face makes the
normalized majorant ratio vanish along its exponential ray. Conversely, a
limiting probability vector of normalized coefficient magnitudes has nonempty
support T. Projecting log coordinates onto the span of differences in T yields
a convergent component because the corresponding linear functionals span that
space. Every outside support point tends strictly below T in the orthogonal
component. One sufficiently late component exposes exactly T as a face. The
limiting signed weight sum supplies a positive zero of that face polynomial.
The whole face and zero polynomial are treated separately. Strict exclusion of
unselected points is necessary and present in the existential encoding.

Fresh independent checks in `root_independent.py` cover 442 signed charts and
14,918 primitive forms through four variables, all 48 Motzkin charts (including
all 16 requiring the explicit sum-of-squares certificate), and the isolated-zero
asymptotic obstruction. All pass with integer or symbolic arithmetic. These
finite checks corroborate the general reasoning; they are not its substitute.
The absent historical software harnesses and claimed solver/compiler run counts
were not recreated or certified by this review; their absence is disclosed in
the submission's current frontmatter.

## AC-11 and AC-12 analytic certificate method

I read the entire final 393-line finite-permanent manuscript. Expanding J-2D by
nonattacking selected entries gives the stated rook-number identity. Its kth
coefficient has valuation n-s2(n-k), at least n-floor(log2(n+1)), yielding the
universal divisor. Thus one independently certified complete matrix attaining
q(n) suffices for each finite minimum claim; cofactor dot products alone do not.

The polarization identity follows because summing signed monomials kills every
term unless each row is selected an odd number of times; degree n forces every
multiplicity to be one. Fixing the first sign correctly halves the sum. Even-row
half-sums are integers. Unsigned wraparound represents arithmetic modulo 2^128;
34!/2<2^127 permits centered reconstruction at the stated search orders. The
separate complete-matrix verifier computes half the permanent modulo both 2^128
and the odd number 2^61-1. Their product exceeds n!/2 plus the absolute claimed
half-permanent through order 35. Matching residues therefore prove exact integer
equality, not merely high confidence. I independently checked all these integer
bounds and the divisor valuations through order 1000.

For AC-12 the two obligations are distinct: verify each restricted witness and
exhaustively contain every unrestricted value. Absolute-value equality implies
signed equality because negating the first row preserves the restricted family.
The normalized lexicographically least core has nondecreasing row masks and
ordered columns. Identical-prefix column blocks permit only the stated sorted
next-row patterns. The orderly test is a necessary property of a global minimum:
otherwise moving a later row earlier and sorting within those blocks decreases
the first differing row without changing prior rows. Coverage, rather than
uniqueness of representatives, is all that is needed.

The prefix-completion bound follows by grouping permutations according to the
columns used by the fixed rows and bounding each complementary permanent by
(n-k)!. A branch can be pruned only when this bound lies within a contiguous
initial progression of already verified multiples of q(n). The universal divisor
then covers every possible completion. If zero is absent or a gap occurs, the
progression and pruning threshold must stop accordingly. These facts justify
the finite exhaustive certificate approach; they do not prove an all-orders
attaining construction or all-orders range equality. AC-11 and AC-12 must remain
Partially resolved at their original IDs and targets.
