# Catalog progress

Target: **1,000 distinct, precise, source-backed open NLA problems**; see
`PROBLEM.md`. Current focus: **PROOF — presentation of the 73 curated problems**,
without solving them. Lean is inactive and not requested.

## Current state — 2026-09-08

**PARTIAL: 73 / 1,000 admitted entries.** The remaining 927 are not supplied.
The [catalog index](CATALOG.md) lists every admitted entry and both
requested ratings. No placeholders, excluded questions, or arbitrary parameter
instances contribute to the count.

The user requested category folders and an individual Markdown/LaTeX/PDF
document for each existing problem. Eight root categories and 73 problem folders
now hold the canonical statements. Shared mathematical definitions have been
copied into the entries that require them; the original chapter pages retain
their anchors and uncounted screening notes.

**COMPLETE: presentation of the existing 73 entries.** All 73 standalone TeX
documents compile to PDF, with no overflow or missing-character warnings. All
76 final pages were visually inspected (70 one-page documents, three two-page
documents). An independent comparison against the original chapters confirmed
the statements, both ratings, status notes, 44 shared-context additions, and
preserved uncounted material. Every problem folder contains exactly its canonical
Markdown, TeX source, and PDF; local navigation links were checked. The small
`tools/render_problems.py` exporter regenerates TeX/PDF from the Markdown.

This export is not a new literature search and does not change the 2026-09-08
screening date. The wider 1,000-problem curation objective remains partial.

- Linear systems and elimination: 9.
- Eigenvalues and inverse problems: 10.
- Matrix functions and stability: 13.
- Randomized and low-rank approximation: 12.
- Tensor computations: 4.
- Nonnegative and positive factorizations: 11.
- Arithmetic and complexity: 9.
- Intervals and absolute value equations: 5.

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

Epperly's 2025 dissertation was checked against his August 2026 RPCholesky
analysis. Its earlier oversampling conjectures are excluded, while RA-01–03
state the surviving sharper pivot count, exactly-r-step error factor, and
randomized-LU factor questions. AV-03 is the polynomial-time P-LCP problem
in equivalent AVE form and is counted once; a June 2026 parameter-dependent
algorithm does not settle the input-length-only target. These six entries
received independent source and quantifier audits.

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
