# Open problems in numerical linear algebra

## Objective

Maintain a collection of **200 distinct open problems in numerical linear
algebra**, extracted from books and research publications. Each entry must state
a precise mathematical question and give a brief set of primary references.

Every entry carries exactly one difficulty label — **hard**, **challenging** or
**extreme** — and one importance rating — **interesting to specialist**,
**interesting to the community** or **broadly interesting**. These are editorial
judgments, explained by a short rationale, not ratings attributed to the authors.

Current focus: **PROOF**, used here for human-readable mathematical curation and
status verification. Lean is inactive. There is no campaign to solve catalog
problems. Short arguments needed to establish an entry's mathematical status
are within the separately requested status audit; label their evidence precisely.

## Scope and deliverables

- Root category folders, each with an index and one subfolder per problem using
  a stable identifier. The root README and `CATALOG.md` provide navigation.
- A canonical `README.md`, standalone `problem.tex` and compiled `problem.pdf`
  per retained entry. Each must include enough definitions to be understood
  independently, and all three formats must state the same mathematical target.
- A precise statement with assumptions, fields, quantifiers and any required
  computational model; motivation; both ratings and their rationale; primary
  references with exact locators where available; status and a dated check.
- Clear separation of open targets, substantive partial resolutions, complete
  solutions, solution claims and candidates needing verification. Only **Open**
  and **Partially resolved** entries count toward 200.
- Contributor instructions for proposing problems or corrections through GitHub
  issues and for submitting complete changes through pull requests. Provide
  practical issue and PR templates and explain document regeneration.
- A durable source screen and progress record stating the actual count,
  literature coverage and unresolved verification limits.

Core NLA includes linear systems, least squares, eigenvalue and singular-value
computation, matrix functions, numerical stability, conditioning, low-rank
approximation and tensor methods. Directly relevant matrix theory and algebraic
complexity are included when their numerical connection is explained.

## Admission and status standards

Use original restatements supported by primary publications. Do not invent
conjectures, convert vague research directions into arbitrary quantitative
claims, count equivalent formulations twice, or split parameter cases merely
to increase the count. Related questions can be distinct, but explain known
implications; stronger bounds on the same target normally belong in one entry.

Check original statements against current versions and later publications,
including proofs, counterexamples and unpublished full-resolution claims.
Historical open status alone is insufficient evidence of current openness.
Record known cases and the limits of the search. Failure to locate a solution
is not a proof that none exists. Do not classify a result for a different model,
field or computational objective as resolving the displayed target.

A solved or claimed-solved problem retains its ID and its original statement,
with the outcome, date and resolution reference made visible, but is excluded
from the open count. Undecided admissions do not count. Never recycle a retired
published ID. `RESOLVED.md` indexes the retained outcomes and screened claims.

## Current requests and completion

The 2026-09-10 expansion request is to bring the collection to 200 open targets,
frame the repository around that maintained collection, and explain how to
contribute through issues and PRs. The concurrent audit request rechecks the
existing entries' statements, status and both ratings and exposes those statuses
in the Markdown, PDFs and indexes. Repository visibility is a separate user
choice and is not changed by these tasks.

The [expansion screen](proof/EXPANSION-TO-200-2026-09.md) records 42 additions.
The audit removes MI-13 from the former 159 open targets, giving
**159 − 1 + 42 = 200**. MI-13's status follows a published refined commutator
inequality and an elementary reduction, independently reviewed by two Codex
agents; this is not an external peer review, Lean proof or novelty claim. IE-01
is retained as a full solution claim following the user's Forsythe correction.

Completion requires the 200 admitted targets, a statement-specific audit of
source fidelity, distinctness, assumptions and known resolutions, synchronized
Markdown/TeX/PDF files, updated indexes and contribution guidance, and a committed
and pushed GitHub state. `PROGRESS.md` distinguishes mathematical admission from
pending rendering or publication work.
