# Catalog progress

Current objective: **200 distinct, precise, source-backed open NLA problems**;
see [PROBLEM.md](PROBLEM.md). Focus: **PROOF — curation and status verification**.
Lean is inactive. No conjecture-solving campaign is requested.

## Current state — 2026-09-10

**COMPLETE: 200 open targets in 11 categories, with a full status and rating audit.**
The integrated export contains **202 Markdown/TeX/PDF sets and 263 PDF pages**,
including the two retained entries outside the open count. All final pages were
visually inspected; the latest builds have no overfull-box or missing-character
warnings. Status and check dates agree between each canonical page and its PDF.
Index and canonical-page local links were checked.

The collection retains **202 problem folders**: 200 with open targets, MI-13
marked **Solved**, and IE-01 marked **Solution claimed**. Only **Open** and
**Partially resolved** statuses contribute to the 200. Every entry has canonical
Markdown, both editorial ratings with rationale, a status and a dated literature
check; the integrated export synchronizes the standalone TeX and PDF versions.

| Category | Open targets |
| --- | ---: |
| Linear systems and elimination | 21 |
| Eigenvalues and inverse problems | 23 |
| Matrix functions and stability | 23 |
| Randomized and low-rank approximation | 27 |
| Tensor computations | 26 |
| Nonnegative and positive factorizations | 12 |
| Matrix inequalities and norms | 28 |
| Frames and matrix designs | 11 |
| Matrix discrepancy and optimization | 6 |
| Arithmetic and complexity | 14 |
| Intervals and absolute value equations | 9 |
| **Total** | **200** |

## Current expansion and audit

The [expansion screen](proof/EXPANSION-TO-200-2026-09.md) records **42 new
admissions**, exact primary locators, distinctions from existing problems,
rejected resolved candidates and remaining access limits. Three parallel
literature searches and independent cross-reviews covered the new statements.
The earlier 159-entry collection loses MI-13 from its open count, giving
**159 − 1 + 42 = 200**. No placeholders or arbitrary parameter cases count.

New coverage includes exact interval solution hulls, incomplete factorizations
for Neumann systems, block-Toeplitz conditioning and eigenvalue expansions,
quadratic and low-rank measurements, generalized permanents, graph inverse
spectra, matrix-function inequalities and tensor norms and ranks. The screen
explicitly records the one-way implication between the two separately posed
asymptotic-rank questions. It does not claim exhaustive book coverage.

The [completed full-catalog audit](proof/STATUS-AUDIT-2026-09-10.md) records
**114 Open, 86 Partially resolved, one Solved and one Solution claimed**.
It reviews status, difficulty and importance separately, changes 29 rating labels
on 27 existing entries, and recalibrates nine new draft entries. Every entry
includes a rationale and exact known-case boundaries. The full and category
indexes show status; the [resolution archive](RESOLVED.md) keeps solved targets
and unverified complete-solution claims visible. **MI-13 is settled by a published
complex refined commutator bound plus an elementary rectangular-to-square
reduction.** Two independent Codex-agent reviews checked the argument's
assumptions and edge cases. This is status verification, not external peer
review, a Lean verification or a claim of mathematical novelty. Its retained
entry contains the argument and evidence.

**IE-01 remains outside the open count.** Colbrook, Stepaniants and Townsend's
[September 2026 manuscript](https://arxiv.org/abs/2609.04659) claims a complete
resolution of Forsythe's conjecture: the restart-three result and counterexamples
at every restart length at least four. The user identified this missed source.
The stable page is restored with **Solution claimed** status and links to the
resolution, rather than presented as an open problem.

The proposed sharp Paulsen distance bound is withheld after
[Lau–Ramachandran, §7](https://arxiv.org/html/2510.13751v1), announces forthcoming
work closing the remaining dimension factor. The current paper does not contain
that full proof. Other exclusions include recent permanent anticoncentration,
nonnegative Kronecker-square counterexamples, refuted Lee-constant formulas,
and resolved determinant or Toeplitz questions. They are documented in the
source screen without treating unpublished claims as independently verified.

The repository-facing text describes the maintained collection. Contribution
instructions and issue/PR templates explain source requirements, duplicate and
solution checks, ratings and document generation. GitHub issues are enabled.
Repository visibility remains private unless the user explicitly chooses
otherwise.

## Durable earlier source records

- [Further literature screen](proof/LITERATURE-EXPANSION-2026-09.md): 12 additions
  that brought the catalog from 147 to 159; the 12 PDFs were one page each and
  were visually reviewed. The then-current export had 159 PDFs and 164 pages.
- [Supplied proposal screen](proof/ADDITIONAL-PROBLEMS-SCREEN.md): all 43 supplied
  candidates, including 22 new entries, 15 duplicates or already covered leads,
  one stronger RIP target grouped in FR-01, and five withheld candidates. The
  original proposal remains in `proof/proposals/ADDITIONAL_PROBLEMS.md`.
- [Wider source screen](proof/WIDE-SEARCH-2026-09.md): the prior 50 additions,
  source corrections, grouped variants, resolutions and uncounted reserves.
- [Higham 2002 screen](proof/HIGHAM-2002-SCREEN.md): the supplied book leads,
  three admitted growth questions and exclusions or model ambiguities.
- [Source coverage](proof/SOURCES.md): books and specific passages examined,
  historical exclusions and reasons uncounted leads require further work.
  Former chapter pages in `proof/catalog/` preserve useful older anchors.

Historical counts in these screens describe their batches, not the current
catalog. Existing exclusions and partial-result restrictions remain binding;
old chat suggestions are not a pending queue.

## Remaining work

The requested expansion, status/rating audit, contribution guidance and solved-
problem display are complete. No Pro review is active (`PRO_REQUEST.md` is CLOSED).
The coherent changes are committed and pushed together on `main`.

After delivery, future contributions should follow `CONTRIBUTING.md`. New
admissions require the same source, duplicate and current-status checks; solved
entries stay visible and are excluded from open counts. Full-book coverage is
unfinished, and bounded literature searches do not certify openness.
