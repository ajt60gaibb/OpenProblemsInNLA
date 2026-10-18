# TR-14: complete exact-rank equality for complex Hankel tensors

The [shared final theorem](../../../../lean-statements/NLA/Proofs/TR14/Final.lean)
now proves the unchanged `NLA.Statements.TR14.Target`: for every m>=3, n>=2,
every complex moment vector and every natural width, ordinary and symmetric
width predicates agree. Zero, exceptional tensors, width zero and arbitrary
mode-dependent ordinary factors are included. The local full theorem passes
LeanCert kernel trust and reports only `propext`, `Classical.choice` and
`Quot.sound`. Independent fresh shared/canonical audits pass 79/83 Lean
commands, with 451/453 declaration checks and 353/355 theorem-kind checks.
All 42 actual private constants are checked directly. Actual isolated Linux
Comparator verification is pending. The canonical page
remains Solved; the user's campaign remains active and incomplete.

## Exact statement and original sources

The live and separately frozen statements remain byte-identical to the published
boundaries. Two fresh preproof statement/route approvals precede new proof bodies:
[campaign review 1](campaign-2026-10-18/independent-review-1/PREPROOF_STATEMENT_REVIEW_1.md)
and [campaign review 2](campaign-2026-10-18/independent-review-2/PREPROOF_REVIEW_2_2026-10-18.md).
All 39 retained candidate modules are preserved unchanged. A separate canonical
Challenge received [boundary review 2](../../../../tensor-computations/TR-14/lean/reviews/PACKAGE_BOUNDARY_REVIEW_2_2026-10-18.md)
and [boundary review 3](../../../../tensor-computations/TR-14/lean/reviews/PACKAGE_BOUNDARY_REVIEW_3_2026-10-18.md)
before Solution was created.

The original canonical README, problem TeX/PDF and solution TeX/PDF were archived
byte for byte from published commit `36767fa430309f13d04dc6ebe080d470f5c2444a`
at [originals-main-36767](originals-main-36767/). The
[preservation checker](check-preservation.py) compares all 217 registered
canonical pages and their immediate original artifacts to the campaign base.
Its pre-Linux run passes all three checks, with all 828 original files unchanged.
The permanent ID, canonical path, mathematical target and credits are retained.

## Actual construction

An actual normalized least-apolar polynomial is chosen for nonzero data.
The exact same chosen chart and modulus are used throughout the upper and lower
proofs. The local CRT/Fourier construction and the separable binary apolar pencil
produce actual finite symmetric decompositions. The latter uses a proved
Wronskian finite-exclusion argument, actual inverse quotient polynomial, actual
Vandermonde weights and exact moment recurrence reconstruction.

The ordinary lower bound starts from an arbitrary supplied width, finds an
actual minimum ordinary decomposition and proves its rank-one coordinate
functions independent by exact deletion/reweighting. Actual graph spaces record
the unrestricted mode functionals. Separate actual units normalize each graph
space; no factor entry is required to be nonzero. Products of all but one actual
mode space surject onto the quotient by an explicit power-basis span argument.

The contextual product inequality constructs its auxiliary spaces/algebras by
finite-dimension induction. A proved finite-subspace avoidance argument selects
a spanning unit class. Auxiliary algebras are proved reduced from the actual
Frobenius/annihilation context. Only reduced subalgebras are counted; ambient
nilpotents are retained. Primitive indicators come from a genuine complex
algebra equivalence. Actual scalar projection and nonzero functional coefficients
exclude scalar-only primitive blocks.

Each intrinsic block is the actual quotient by its complementary idempotent.
Its inclusion is a genuine linear equivalence to the ambient multiplication
image. All context hypotheses pass through these actual maps, and extending a
block stabilizer by zero proves it is scalar by primitive action. Actual cyclic
polynomial-image dimensions give min(n,block dimension); a nonzero functional
supplies codimension one. Genuine orthogonal multiply/sum equivalences partition
the ambient dimensions. Whole local CRT factors are zero or one under each
idempotent, giving the root-support count. These proved data imply the ordinary
lower bound by finite arithmetic. The final theorem chooses the smaller actual
symmetric width, transports the ordinary witness in the same chart and pads back
to the requested original width. Zero data and scalar absorption are direct.

The stronger projective-root rank formula from the submitted resolution is not
substituted for the original target and is not separately exported. There is no
conditional lower-bound oracle in the full theorem.

## Independent evidence and canonical package

Independent source reviews distinguish each agent's authored modules from their
other-author review scope. Retained reports include:

- [Binary construction](BINARY_CONSTRUCTION_INDEPENDENT_REVIEW_3_2026-10-18.md),
  [reconstruction](BINARY_RECONSTRUCTION_INDEPENDENT_REVIEW_3_2026-10-18.md) and
  [same-chart upper bounds](CHART_UPPER_INDEPENDENT_REVIEW_3_2026-10-18.md).
- [Contextual/classification/minimum source review by root](CONTEXTUAL_CLASSIFICATION_MINIMUM_REVIEW_ROOT_2026-10-18.md)
  and [independent contextual/minimum audit](CONTEXTUAL_AND_MINIMUM_INDEPENDENT_REVIEW_3_2026-10-18.md).
- [Actual graph/context/block-image review](GRAPH_CONTEXT_AND_BLOCK_IMAGE_REVIEW_2_2026-10-18.md),
  [corner and separation review](CORNER_AND_SEPARATION_SOURCE_REVIEW_2_2026-10-18.md),
  [primitive scalar stabilizer](CORNER_STABILIZER_INDEPENDENT_REVIEW_3_2026-10-18.md)
  and [inherited block inequality](CORNER_INHERITANCE_SOURCE_REVIEW_2_2026-10-18.md).
- [Whole-factor support and dimension partitions](BLOCK_SUPPORT_AND_PARTITIONS_INDEPENDENT_REVIEW_3_2026-10-18.md)
  and [complete normalized ordinary lower review](NORMALIZED_ORDINARY_LOWER_REVIEW_2_2026-10-18.md).

The [canonical package](../../../../tensor-computations/TR-14/lean/README.md)
has 78 byte-identical shared source copies (76 proof modules and two statement/
infrastructure modules), with Reviewed and the three boundary/export modules,
for 82 actual Lean inputs. The [reproducible copy/lock checker](sync-canonical-proof.py)
checks all copies and eight explicit exports. Challenge has one deliberate
comparison placeholder and is not imported by Solution. Identity proves frozen
statement equality by rfl. Comparator selects exactly the unchanged full Target,
with no definition holes and only the standard three permitted axioms.

The [full independent shared review](FULL_TARGET_INDEPENDENT_REVIEW_3_2026-10-18.md)
and [canonical fresh closure evidence](verification/canonical-target-review-3/result.json)
check the literal unchanged target, all declarations and theorem kinds, actual
private constants, kernel trust and standard axioms. The separate
[complete Final review](FULL_TARGET_FINAL_REVIEW_2_2026-10-18.md) and
[Final/canonical source review](FINAL_AND_CANONICAL_SOURCE_REVIEW_1_2026-10-18.md)
distinguish each author's implemented prerequisites from independent review.

Fresh local source/kernel/axiom/theorem-kind checks are distinct from actual
isolated Linux Comparator verification. No Linux result is claimed yet.
The standard workflow will check the committed package and rejection/isolation
controls and retain exact input hashes. All reviews are by AI agents; no external
human peer review or source-author participation is claimed. Mathematical credit
remains with Sidney Holden's submitted proof, Beck--Lecouvey's transformation
lemma, and Nie--Ye/Qi's original problem context.
