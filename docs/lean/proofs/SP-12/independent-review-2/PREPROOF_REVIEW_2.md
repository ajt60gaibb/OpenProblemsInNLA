# SP-12 independent preproof statement and source review 2

Reviewer: OpenAI Codex agent `/root/solved_inventory` (AI), 18 October 2026.
Source checkout: `/private/tmp/nla-sp12-lean-oct18`, immutable starting revision
`d08d73a31594594a0024fbf78fec5eec291b30ce`.

**APPROVE the unchanged SP-12 specification and live/frozen Lean boundary for
implementation. No source mathematical blocker found. This is not approval of an
implemented SP-12 proof, which does not yet exist.** I did not author these
SP-12 statement definitions, canonical sources or numerical specification. I read
them before exchanging conclusions with the other current SP-12 reviewer. I did
not read that reviewer's new findings before writing this report. I implemented
some SP-11 support modules, so the reuse analysis below is not an independent
review of my own SP-11 proof implementation.

`input-lock.json` records every reviewed local source hash and its exact retained
copy under sources/. The canonical README and ORIGINAL are identical:
`cdc8003bc5160604408ce6b95c344a4ea1b9bfbf8af0f99ae1e8e016648d53e1`.
The exact live statement is
`c41acae980a06e3f1e8d59e2c552f85812c521ed5e66473b74e01542bfd80f2b`,
and the frozen reviewed statement is
`adfb89f439ce5e2959aaeeb4b3ef6c432bf38f364567765715fdd8f9a1510d86`.
The only intended live/frozen differences are namespace and frozen-boundary
comment; the mathematical definitions match. No canonical source, permanent ID,
registry path, original, historical credit or proof body was changed. Separate
statement-build evidence checks only the unchanged existing definitions, not a
new SP-12 proof.

## Exact statement semantics

The retained target quantifies over every natural n>0 and every simple graph on
Fin n. Its witness is a real n by n matrix. HasPattern supplies symmetry on every
entry and nonzero iff adjacency on every distinct pair. Both implications are
present. There is no prescribed diagonal, edge sign, connectedness, regularity,
vertex-criticality, positive degree, PSD relaxation or SAP relaxation.

NonnegativeQuadraticForm quantifies over every real vector and uses the exact
double sum of x_i A_ij x_j. Combined with HasPattern's symmetry, this is ordinary
real positive semidefiniteness. It is not entrywise nonnegativity or a condition
on a chosen vector. A future Matrix.PosSemidef bridge must preserve the separate
symmetry condition; the pinned API posSemidef_iff_dotProduct_mulVec provides the
appropriate Hermitian plus all-vector quadratic-form formulation over the reals.

StrongArnold quantifies over every real symmetric matrix X. Its three premises
are ordinary matrix multiplication A*X=0, the scalar identities A_ij*X_ij=0 for
all entries (the exact Hadamard equation), and zero diagonal of X (the exact
I Hadamard X equation). They are distinct. Zero diagonal of A is not required.
No conclusion, SAP witness or restricted test space is supplied as an argument.

ChromaticNumber is the natural sInf of actual proper color functions
Fin n -> Fin c. The admissible set contains n by the identity coloring, and no
function from inhabited Fin n to empty Fin 0 exists. Thus the infimum is achieved,
chi>=1 and chi<=n, with no empty-infimum convention. Natural chi-1 agrees with the
intended difference. A bridge to Mathlib's ENat-valued chromaticNumber must prove
this precise equality and finite conversion, rather than replacing the frozen
custom definition. Matrix.rank and natural n-rank are the reviewed real rank and
exact nullity; square rank is always <=n.

The existential matrix formulation is the original inequality for the maximum
PSD/SAP nullity: attainable nullities lie in the finite set 0,...,n. Feasibility
is nonempty, for example a positive-definite matrix with the exact pattern gives
SAP because invertibility already forces X=0. A Laplacian plus identity supplies
such a pattern. This equivalence explains the original maximum convention; the
Target itself correctly avoids assuming an unexplained graph invariant.

The n=1, chi=1, isolated, disconnected and rank-zero cases remain included.
For an edgeless graph with multiple vertices, a completely zero matrix generally
fails SAP, since a symmetric off-diagonal X survives. A proof must not use that
matrix as an automatic SAP witness. Identity works for the chi=1 edgeless base
case. Empty induced subgraphs may occur in helper statements, but the selected
critical subgraph for positive chi can and should be shown nonempty.

## Primary mathematical source cross-check

I reopened the versioned [Hall primary text](https://arxiv.org/html/2601.01211v1),
including the exact SAP definition, uniform LSS success criteria, upper-zero
condition, Theorem 3.12, main theorem/corollaries, hanging-garden definitions,
Unique Monomial Lemma and final deduction. Hall's route needs independence of
earlier nonneighbors, not general position of every small vertex subset. Full
general position has a connectivity obstruction and cannot simply be added at
the delta dimension. The upper-zero condition implies SAP by taking the last
nonzero test-matrix column. Strong success supplies this local independence and
faithfulness. The diagonal/edge polynomial noncancellation and simultaneous
specialization are exactly the pieces now formalized in SP-11. The abstract's
positive-definite wording conflicts with its nonzero-nullity aim; the definitions
and construction consistently require positive semidefinite matrices. No proof
should follow the abstract's wording instead of the formal definitions.

The original [Barioli–Fallat–Gupta–Li primary paper](https://arxiv.org/html/2505.24577v1),
Definition of nu in Section 1 and Conjecture 4.1, uses the same real PSD/SAP
invariant and exact chi-1 target. Its graph-degeneracy discussion identifies the
high-minimum-degree subgraph step. The canonical application note supplies the
induced-subgraph extension and critical-subgraph deduction, not a replacement
for Hall's central theorem. Mathematical credit remains Hall; Stepaniants is the
application-note author, with no human-referee or source-author participation
claim.

## Concrete reuse and missing formal interfaces

These are implementation recommendations deduced from the actual pinned Lean
sources, not claims that the interfaces have already been proved.

1. Reuse SP11.Final.polynomialLSS_nonzero, polynomialLSS_nonedge, the simultaneous
   real evaluation lemma, exact Gram pattern/rank bounds and greedy permutation
   data. The opaque final SP11.Target witness alone discards the LSS representation
   and does not supply SAP. Retain the evaluation point and actual polynomial rows
   through the lower-level existence result.
2. Establish that evaluation of the concrete universal determinant forms commutes
   with alternating contraction and the uniform recursion. Equivalently define
   the real vertex forms with evaluated shared tensor coefficients and prove the
   evaluated rows are their actual uniformLSS. The current SP11 APIs prove Gram
   evaluation, but do not yet export this real-form recurrence.
3. A nonzero contraction forces linear independence of its input family. The
   pinned AlternatingMap.map_linearDependent already proves alternating evaluation
   vanishes on a dependent tuple. If all row coordinates vanished, the contraction
   would be zero; conversely a nonzero coordinate gives a nonzero alternating
   evaluation on that coordinate basis vector plus the inputs, hence independence
   of the inputs by restriction. This needs a new small algebraic bridge, not a
   new noncancellation proof. SP-11's chosen evaluation already makes every row
   nonzero, so it should give the needed prior-nonneighbor independence.
4. Prove PSD of the actual Gram matrix and the exact frozen quadratic-form bridge.
   Reuse Matrix.posSemidef_self_mul_conjTranspose or prove the quadratic sum is a
   sum of squares. The existing SP11.gram R = R*R.transpose is already suitable.
5. Prove SAP from actual prior-nonneighbor independence. One route passes through
   invertibility of the corresponding principal Gram matrices, then upper-zero
   independence of full Gram columns. Another directly uses a last nonzero column
   of X: its support is earlier nonneighbors; A*X=0 for the Gram implies the
   corresponding linear combination of representing vectors is zero by positivity;
   local independence makes the column zero, a contradiction. No full general
   position, global full row rank or independence at every arbitrary subset is
   needed. Reindex SAP and PSD through the actual Fin permutation as well.
6. The high-degree critical induced subgraph and its chromatic-number facts are
   still unimplemented. Build a minimum-cardinality induced vertex set with chi
   unchanged; extending a (chi-1)-coloring after deleting a vertex of degree <=chi-2
   gives the contradiction. The finite infimum and custom-to-Mathlib colorability
   bridges must retain the exact frozen natural ChromaticNumber.
7. Induced extension is the major remaining analytic obligation. Block-diagonal
   padding works only for an added isolated vertex and fails the prescribed new
   edge pattern in general. The source note's fixed-rank PSD manifold argument
   can be recast with a Gram factor C of A. The off-nonedge map C -> off(C*C^T)
   has derivative D -> off(D*C^T + C*D^T). Its adjoint kernel is exactly the SAP
   test space: a symmetric off-nonedge-supported X annihilating C. Positivity
   identifies this with A*X=0. SAP therefore gives surjectivity. A finite-dimensional
   local right inverse can impose the required small old-nonedge corrections.
   Adding the new row/coordinate produces the exact graph with rank at most r+1,
   preserving the required nullity bound. SAP of the extended matrix still needs
   a proved openness/full-column-minor argument. This replaces a rank-manifold
   formalization, but does not make induced monotonicity automatic.

For the extension, rank at most r+1 is sufficient for the lower nullity bound;
constant rank equality of every nearby factor is unnecessary. New-edge entries
must use an actually nonzero sufficiently small parameter; old-edge entries stay
nonzero by continuity, and old nonedges must cancel exactly. SAP openness must be
on the fixed graph-supported test subspace. Rank zero, zero-dimensional correction
spaces and isolated added vertices must be covered explicitly. The final graph
need not be connected.

## Pinned API audit and implementation gates

Local source search in pinned Mathlib found no StrongArnold/upper-zero/nu graph
parameter implementation and no direct critical-subgraph chromatic-degree theorem.
Relevant existing APIs are AlternatingMap.map_linearDependent
(LinearAlgebra/Alternating/Basic.lean), the Matrix Gram positive-definiteness and
linear-independence equivalences in Analysis/InnerProductSpace/GramMatrix.lean,
Matrix.posSemidef_iff_dotProduct_mulVec and Gram PSD multiplication lemmas,
SimpleGraph.Colorable.chromaticNumber_eq_sInf, chromaticNumber_le_iff_colorable,
colorable_chromaticNumber_of_fintype, colorable_zero_iff, and the Laplacian PSD
lemma. The Mathlib chromatic number is ENat; this distinction is material.

Implementation may proceed after the two independent preproof approvals, but
must keep each new semantic bridge explicit. First complete the strong-delta
PSD/SAP witness from the actual SP-11 representation; independently implement the
chromatic critical-subgraph and induced-extension arguments; then assemble the
unchanged Target. None of these may be an axiom, assumed literature theorem or
favorable supplied invariant. All final sources require kernel mode, complete
axiom/sorry closure, complementary independent source reviews and actual Linux
Comparator evidence. IDs, originals and canonical status remain unchanged until
that final evidence exists.
