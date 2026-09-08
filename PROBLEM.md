# 1,000 open problems in numerical linear algebra

## Objective

Turn this GitHub repository into a collection of **1,000 distinct open problems
in numerical linear algebra (NLA)**, extracted from books and research
publications. Each entry must give a precise, well-defined mathematical
statement and a brief set of references.

Every entry must carry exactly one difficulty label: **hard**, **challenging**,
or **extreme**; and exactly one importance rating: **interesting to specialist**,
**interesting to the community**, or **broadly interesting**. These are editorial
assessments, not claims made by the cited authors.

Check whether each proposed problem has already been solved. The user's final
sentence is interpreted in the context of an *open*-problem collection: exclude
resolved questions, and describe partial resolutions that limit the surviving
statement. A historical open-problem citation alone does not establish current
openness. Record the date, sources, and scope of the literature check. Absence of
a found solution is evidence with a stated limit, not a proof of openness.

## Scope and deliverables

Focus: **PROOF**, used here for human-readable mathematical curation and
literature verification. No solutions, proof attempts, CAP, or Lean development
are requested. Preserve existing template materials without maintaining an
inactive formalization track.

- Category folders at the repository root, each containing an index and one
  subfolder per admitted problem, with stable problem identifiers. The root
  README and `CATALOG.md` provide category and full-collection navigation.
- For every admitted problem, a canonical `README.md` suitable for GitHub and
  chatbot reading, standalone `problem.tex`, and compiled human-readable
  `problem.pdf`. Shared definitions must be included locally so each document
  can be understood independently. The three formats must state the same problem.
- For each problem: topic, precise statement including assumptions and
  quantifiers, difficulty, importance, short motivation, primary references with
  locators where available, and a dated status check.
- A clear distinction between admitted open problems, candidates whose status
  needs more evidence, and resolved/rejected historical problems.
- A durable progress record giving the actual count against the target of 1,000.

The category organization and Markdown/LaTeX/PDF export are complete. The latest
request is a wider literature search using six subagents, aiming to add **50 more
distinct, precisely stated NLA conjectures from books or papers**, with the same
status checks, ratings, and Markdown/TeX/PDF deliverables. This batch is complete:
50 entries were added to the starting 75,
for **125 admitted entries**. The [wider screen](proof/WIDE-SEARCH-2026-09.md)
records the six searches and admission decisions. The earlier Higham screen
added IE-13–15;
`proof/HIGHAM-2002-SCREEN.md` records its supplied leads' dispositions.
IE-01 remains removed following the September 2026 resolution of Forsythe's
conjecture. Maintain accurate counts and retain resolution references in the
source record and former chapter pages in `proof/catalog/`, which preserve old
anchors and uncounted material.

Start with core NLA: linear systems, least squares, eigenvalue and singular-value
computation, matrix functions, numerical stability, conditioning, low-rank
approximation, and numerical tensor methods. Directly relevant matrix theory and
algebraic complexity may be included with their numerical connection explained;
this broad scope is the working interpretation in the absence of a narrower user preference.

## Admission and completion

Use original restatements supported by primary literature or books. Do not
invent conjectures, inflate the count using equivalent formulations or arbitrary
parameter instances, treat a vague research direction as a precise problem, or
count a solved problem as open. An undecided candidate does not count toward the
target.

Completion requires 1,000 distinct admitted entries meeting all requested
conditions and a target-specific audit of statement fidelity, duplication,
scope, and known resolutions. A smaller collection is partial progress, even
when its entries are high quality. No proof of any catalog problem is part of
the deliverable.
