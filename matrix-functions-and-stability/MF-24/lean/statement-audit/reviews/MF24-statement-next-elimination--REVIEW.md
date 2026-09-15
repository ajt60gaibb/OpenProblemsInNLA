# MF-24 independent statement referee

Reviewer `/root/next_elimination`, 15 September 2026, separate from the MF-24
statement author. I made no edits to MF-24 and ran no local Lean/Lake command.
This is scoped Tau Ceti style AI review of mathematical fidelity, definitions,
quantifiers, numerical reductions and trust separation, not external human
peer review or official Tau Ceti endorsement.

**Approve all 22 proposed statements and the explicitly documented quantitative
simplification. No mathematical target correction is requested.** Actual Linux
statement elaboration and the other independent approval are still required
before freezing or authorizing proof implementation. This review supplies no
mechanical acceptance and increments no verified-problem count.

I read the canonical MF-24 page, the retained reference README and complete
Maierhofer manuscript directly from immutable upstream
`8f04b905eb2e0827b6b84f37d9d080ae1f05b202`. I read Definitions, every Challenge
declaration, numerical targets and source correspondence in full. Independent
source hashes, exact copies and the primary Mathlib API excerpts are retained
with this report. The source provenance hashes match my own `git show` reads.

The original target is the existence of one uniform polynomial norm comparison
constant over every positive dimension, every super-identical pair and every
complex polynomial. UniformComparison states precisely that target; requiring
the putative constant to be positive loses no possible uniform bound. The
stronger finite-family export demands a genuine witness above every C≥0 and
explicitly includes a nonzero denominator. No totalized unbounded real
supremum or zero denominator supplies the final negation.

The norm is explicitly that of Matrix.toEuclideanCLM, a continuous map on
complex Euclidean space. I inspected the pinned CStarAlgebra/Matrix source:
the conversion agrees with matrix multiplication on WithLp vectors and its
norm is the induced Euclidean operator norm. This avoids accidental entrywise
or Pi supremum norms. singularValue uses the actual Mathlib singularValues of
the corresponding Euclidean linear map. The pinned SingularValues source
defines the nonnegative square roots of the adjoint-composition eigenvalues,
in descending order with multiplicity, padded with zero after finite rank.
Its first N indices are exactly the required full N-element singular list.
The Gram-to-singular bridge retains repeated eigenvalues, multiplicities,
zeros and the zero matrix. The pinned Matrix/Spectrum source provides sorted
characteristic-root/eigenvalue identities, so this is a tractable genuine
semantic bridge, not a redefinition of SIP as characteristic equality.

SuperIdentical quantifies every complex shift, and polyEval is actual complex
polynomial evaluation in a matrix algebra. No domain restriction, sampled
shift set or special polynomial class replaces these definitions. The witness
family alone is real nonnegative and nilpotent, as in the original proof;
the final uniform claim still ranges over all complex matrices.

The two word definitions agree exactly with the source motif and bridge
ordering. Their full lengths and growing dimension are separate obligations.
The height ratios are not silently installed as the witness matrices: a
required theorem identifies them with the original word-defined shifts.
Natural truncation in m−1 is harmless because all family assertions require
m≥2. getD's default zero cannot replace an intended edge after the required
length theorem. The height-shift power formula includes exponent zero and
every entry, with positive t ensuring all divided powers are nonzero.
The fixed polynomial has all and only the m forward stride multiples, degree
N−1 and zero constant term. Its evaluation and every entry must be proved.

The generic leading determinant really is the leading block of the shifted
Gram matrix: A* A for an upper shift has diagonal |z|² plus the incoming edge
square, not the outgoing edge square. Thus truncating the word-shift dimension
retains exactly the required first j−1 edges. Both determinant base cases and
the entire valid-prefix recurrence are present, including zero and negative
real weights, all complex z and all complex η. The reversed transfer list
correctly puts later edges on the left. The bridge has arbitrary complex P
and all scalar parameters, no inverses or conjugate transpose. I independently
expanded the compressed n=1 commutator and the two-by-two Cayley–Hamilton
identity as integer-coefficient sparse polynomials; all coefficients cancel.
The all-n deduction by Cayley–Hamilton therefore has the source's actual
algebraic content. Equality of every η evaluation must still be converted to
actual Gram characteristic-polynomial equality in Lean.

The first-row energy is genuinely t⁴m, and the polynomial denominator is
required to be nonzero. These are not substitutes for the subsequent actual
operator-norm bounds. Every residue class retains all its vertices and the
unique partition covers the complete space. Each class has size at most m+1,
at most one height zero and at most one height two. Since 0≤height≤2 and t>1,
the inverse-weight sum is at most 1+m/t² and the forward-weight sum at most
t⁴+mt². Their product is exactly (t²+m)². Bounding every within-class
nonnegative entry by the full outer product and applying finite
Cauchy–Schwarz yields the claimed energy inequality for every COMPLEX
Euclidean vector. No row deletion, positivity restriction on the input vector
or block-size sample is hidden in that assertion.

The resulting denominator bound t²+m is weaker than the manuscript's
t²+m−1, but it preserves the complete canonical negative answer. At the
finite rational choice t=m, m≥2 gives 1/(1+1/m)≥2/3, hence the norm ratio is
at least (2/3)√m. Choosing a natural m above (3C/2)² refutes any prescribed
nonnegative real bound. The canonical page explicitly distinguishes this
uniform-boundedness target from the sharper dimension-dependent constants.
The source's factor 4/5, all-dimension padding, specific C_N lower bound and
liminf corollary are transparently unclaimed, not silently counted as proved.

My independent Fraction checks compare both source words against every
adjacent height ratio, check the full residue partition and all height-count
restrictions, first-row energy, nonzero terminal entry, both full-vector
weight inequalities and their product for m=2,...,20, t=3/2 and t=m. These
finite diagnostics complement the analytic review; they do not discharge any
universal Lean obligation or validate the eventual implementation.

No proof implementation is present. The 22 deliberate Challenge holes are
isolated; Comparator requires all 22 names with no definition holes and only
propext/Classical.choice/Quot.sound. Its actual execution remains mandatory,
as do LeanCert kernel checks, complete axiom audit, separate kernel replay,
negative controls and two independent final code/evidence referees.

Original mathematical credit correctly remains Georg Maierhofer, University
of Cambridge. George Stepaniants receives formalization credit with his
authorized Department of Computing and Mathematical Sciences, California
Institute of Technology affiliation, without email. These are different people.
The proof-size reduction is appropriate: generic continuants, a 2×2 algebraic
identity, exact weighted paths and finite Cauchy–Schwarz avoid factorial
determinant expansion, numerical SVDs and interval subdivision. I found no
known statement-level API mismatch in the inspected definitions; only actual
remote elaboration can establish Lean syntax and instance acceptance.
