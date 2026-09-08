# Catalog progress

Target: **1,000 distinct, precise, source-backed open NLA problems**; see
`PROBLEM.md`. Current focus: **PROOF — curation and status corrections**,
without solving them. Lean is inactive and not requested.

## Current state — 2026-09-08

**PARTIAL: 125 / 1,000 admitted entries.** The remaining 875 are not supplied.
The [catalog index](CATALOG.md) lists every admitted entry and both
requested ratings. No placeholders, excluded questions, or arbitrary parameter
instances contribute to the count.

The user requested category folders and an individual Markdown/LaTeX/PDF
document for each existing problem. Ten root categories and 125 problem folders
now hold the canonical statements. Shared mathematical definitions have been
copied into the entries that require them; the original chapter pages retain
their anchors and uncounted screening notes.

**COMPLETE: presentation of the admitted entries.** The original 73-document
export compiled without overflow or missing-character warnings, and all 76 pages
were visually inspected. Removing the resolved IE-01 leaves 72 documents and
75 previously inspected pages (69 one-page documents, three two-page documents).
An independent comparison against the original chapters confirmed
the statements, both ratings, status notes, 44 shared-context additions, and
preserved uncounted material. Every problem folder contains exactly its canonical
Markdown, TeX source, and PDF; local navigation links were checked. The small
`tools/render_problems.py` exporter regenerates TeX/PDF from the Markdown.

The subsequent Higham source screen adds three one-page PDFs, for 75 documents
and 78 pages total. The new TeX/PDF files compile without overflow or missing
characters; all three new pages were visually inspected. Independent source
review checked matrix fields, bandwidth boundaries, both corner requirements,
pivot ties, the all-stage growth definition, and distinctness. Complex fields in
IE-13–14 follow the adjacent theorem; the exercise itself leaves the field implicit.
The wider 1,000-problem curation objective remains partial.

- Linear systems and elimination: 15.
- Eigenvalues and inverse problems: 17.
- Matrix functions and stability: 17.
- Randomized and low-rank approximation: 17.
- Tensor computations: 13.
- Nonnegative and positive factorizations: 12.
- Matrix inequalities and norms: 12.
- Frames and matrix designs: 8.
- Arithmetic and complexity: 9.
- Intervals and absolute value equations: 5.

All entries include primary references and dated bounded literature searches.
The absence of a found resolution is not a certificate of current openness.
Older-status entries explicitly expose their weaker evidence. Difficulty and
importance are editorial ratings, with definitions in the repository README.

## Mathematical screening findings

**COMPLETE: the requested wider batch of 50 additions.** Six search subagents
covered iterative methods, matrix functions and inequalities, randomized NLA and
frames, tensors, spectral/inverse problems, and structured matrices. The
[durable screen](proof/WIDE-SEARCH-2026-09.md) records exact source passages,
related statements counted together, recent partial results, resolutions,
withdrawals, and uncounted reserves. The new categories expose matrix inequalities
and frame/design questions separately. Root source review covered all 50 additions;
independent audits also checked the tensor, spectral, and structured groups.

The 50 new PDFs contain 51 pages (NM-04 requires two), for **125 PDFs and 129
pages** overall. New documents compile without overflow or missing-character
warnings, and all 51 new pages were visually inspected. The source audit clarified
border-rank limits, rectangular Sinkhorn normalization and every coefficient sign,
entrywise versus Loewner order, generic matrix-nearness data, and the corrected
Toeplitz theorem's conjectural status. No conjectures were solved or attacked.

**Higham notes screened on 2026-09-08:** the
[complete disposition record](proof/HIGHAM-2002-SCREEN.md) covers all 20 numbered
leads, the methodological 26.4 lead, and five prose leads. Added IE-13 (unequal
bandwidth GEPP growth), IE-14 (cyclic tridiagonal GEPP growth), and IE-15 (exact
rook growth in orders three and four, counted together). No later solution was
located; these entries explicitly expose their historical-source status evidence
and the absence of a recent explicit reaffirmation of openness.

The screen found a 2014 published claim resolving Higham's tridiagonal inverse
bound conjecture, so that narrower candidate remains outside the count; it does
not settle the book's full-matrix question. Classical Gram–Schmidt's missing
orthogonality bound has a 2005 answer. Fasi–Hashemi's September 2026 Sylvester
paper is partial progress, while Hashemi–Nakatsukasa's Sherman–Morrison paper
explicitly leaves unconditional bounds open. Those leads need precise surviving
targets or complete arithmetic models. Complete-pivoting asymptotics are
superseded by the August v4 theorem, and the Hadamard part duplicates IE-03.
Corrected the Drury paper link and Teng Zhang's authorship in the source record.
No solutions or proof attempts were made.

**IE-01 removed on 2026-09-08:** the user identified Colbrook, Stepaniants, and
Townsend's [complete resolution of Forsythe's conjecture](https://arxiv.org/abs/2609.04659),
submitted September 4, 2026. Theorem 1.1 covers the former entry: convergence for
$s=3$, counterexamples for every $s\ge4$. The initial screen missed this paper.
Its exclusion note retains the stable ID; its three obsolete files were removed
from the current collection and remain in Git history.

Recent full-solution claims exclude general Crouzeix, polynomial complete-pivot
growth, matrix Spencer, and all restart lengths in the Forsythe question. Higham's
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

The requested 50-entry batch is complete. The broader 1,000-entry target remains
partial, with 875 further distinct admissions needed.

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
