# Catalog progress

Target: **1,000 distinct, precise, source-backed open NLA problems**; see
`PROBLEM.md`. Current focus: **PROOF — literature curation**, without solving
the problems. Lean is inactive and not requested.

## Current state — 2026-09-08

**PARTIAL: 67 / 1,000 admitted entries.** The remaining 933 are not supplied.
The [catalog index](proof/catalog/README.md) lists every admitted entry and both
requested ratings. No placeholders, excluded questions, or arbitrary parameter
instances contribute to the count.

- Iterative methods, eigenvalue computation, elimination: 11.
- Sparse solvers and Krylov query complexity: 3.
- Matrix functions, matrix products, and stability: 12.
- Structured matrix functions: 1; accurate arithmetic: 1.
- Tensors, low-rank approximation, and randomized methods: 8.
- Hierarchical and structured matrix approximation: 5.
- Inverse spectra and structured conditioning: 5.
- Positive semidefinite and completely positive factorizations: 5.
- Exact nonnegative ranks: 4; nonnegative factorization complexity: 2.
- Interval matrices: 2.
- Algebraic complexity and matrix powering: 8.

All entries include primary references and dated bounded literature searches.
The absence of a found resolution is not a certificate of current openness.
Older-status entries explicitly expose their weaker evidence. Difficulty and
importance are editorial ratings, with definitions in the repository README.

## Mathematical screening findings

Recent full-solution claims exclude general Crouzeix, polynomial complete-pivot
growth, matrix Spencer, and the restart-two Forsythe question. Higham's
Fréchet-derivative Jordan-form question has a later solution; his growth-bound
question for complex symmetric matrices was also already answered. The
[source record](proof/SOURCES.md) and chapter exclusions preserve the references.

The August workshop revision reports a full solution claim for the fermionic
kernel question, so former TR-02 is excluded. The August revision of the
structured-matrix-learning paper has an abstract update reporting a resolution
of finite-family relative error, while §5 still contains its old question:
former RE-04 is excluded. Section-only screening can miss these updates.

Independent source audits checked the complexity, iterative, tensor, and
matrix-product drafts. Material corrections included field restrictions,
both residual equations for singular triples, precision-dependent operation
counts, fixed versus simultaneous probability quantifiers, and strict versus
non-strict stability thresholds. IE-09 remains uncounted because its faithful
precision/complexity formulation is unresolved. IE-12 was revised after the
May 2026 version of its source proved the general-system rate with a log n
overhead; only the stated bound without that overhead remains admitted.
Independent audits also checked the HSS/HODLR rank definitions, adaptive query
models, PSD factorization orbits, rigidity with zero entries, nonnegative-rank
conjectures, and interval sign regularity. The exact determinant-range question
is not answered by later methods using a different generalized interval
arithmetic.

Gillis's book supplies precise factorization questions. NM-02, the necessity
of sufficient scattering for minimum-volume uniqueness, is withheld because
a concrete 2021 enclosing-triangle example raises an unresolved compatibility
concern; neither openness nor refutation is claimed. Different SSC definitions
and the presence of a nonnegativity constraint on the other factor matter.
NR-03 fixes every entry of the correlation matrix; July 2026 bounds for a
partial unique-disjointness matrix do not settle this prescribed completion.

The current scope includes directly relevant matrix theory and arithmetic
complexity as well as core NLA. The optional breadth question received no reply,
so work proceeded with this interpretation. The user's target remains 1,000;
no evidence yet establishes that the target can be filled within a narrower
scope without inventing questions or subdividing them artificially.

## Remaining work

Continue source curation in underrepresented core NLA areas, including
randomized estimation, absolute-value systems, least squares, preconditioning,
matrix polynomials, and numerical tensor methods.
Full-book coverage is unfinished. `proof/SOURCES.md` records the actual books
and passages examined, plus useful candidates and precise obstacles.

Before admitting another batch, compare its statements with current primary
versions, check later work for solutions or counterexamples, and avoid counting
equivalent formulations. Update the index, counts, and source record only when
the admitted collection changes meaningfully. No Pro review is active
(`PRO_REQUEST.md` is CLOSED); no review Doc has been created.
