# Contributing

Use [GitHub issues](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues) for
new problem suggestions, missing references, rating feedback and status
corrections. A useful report identifies the problem ID, links a primary source,
and gives a theorem, conjecture or page locator. Use the correction-or-resolution template
when a question may have been resolved.

## Scope and admission

The collection covers linear systems, least squares, eigenvalue and singular-value
computation, matrix functions, stability, conditioning, low-rank approximation
and tensor methods. Matrix theory and algebraic complexity are included when
their numerical-linear-algebra connection is explained.

For a new problem, supply a precise statement, assumptions and quantifiers, its
numerical-linear-algebra connection, proposed difficulty and impact with a short
rationale, and evidence about later solutions. Check for equivalent entries
before proposing another ID. A research direction without a definite completion
criterion needs clarification before admission.

Use an original restatement supported by primary publications. Include the field,
computational model and definitions needed to read the problem independently.
Do not split parameter cases just to add entries; stronger bounds on the same
target normally belong together. Explain known implications between related
questions. Clearly label an editorial formalization of a source question.

Check the source's current version and later publications for proofs,
counterexamples and full-solution claims. A historical open-problem citation
alone does not establish current status. Record known cases, the date and limits
of the search, and the exact question that remains. A result for another model,
field or computational objective does not settle the displayed target.

## Editing an entry

For your first pull request, fork the repository and create a branch. Add the new problem at `category/ID/README.md`, using a neighboring entry as a model. Include `Difficulty`, `Importance`, `Rating rationale`, `Status` and `Last checked`. Propose an unused ID; never recycle a published one. For an existing entry, edit its `README.md`, which is the source of truth.
Keep the mathematical target faithful to its source and distinguish a theorem
from a conjecture or a preprint claim. Use the [rating rubric](README.md#ratings)
and [status definitions](README.md#problem-status). Ratings assess the surviving
open question; historical ratings on resolved entries are explicitly identified.

## Updating indexes and PDFs

The build tools require Python 3; PDF generation also requires Pandoc and XeLaTeX.
After editing an entry, update the indexes and regenerate its documents:

```bash
python3 tools/update_catalog.py
python3 tools/render_problems.py IE-02
```

Replace `IE-02` with the changed problem's ID; several IDs may be supplied.
Omit the IDs to render the whole collection. The index tool rebuilds `CATALOG.md`,
category indexes and the README counts from canonical metadata, excluding solved,
claimed and unverified entries from the open count.

Inspect the resulting PDF and include the Markdown, TeX and PDF changes together.
Each exported TeX file can also be compiled on its own with XeLaTeX. The
[shared typesetting template](tools/problem-template.tex) controls appearance;
the renderer supports `PANDOC` and `XELATEX` executable overrides.
Open the pull request against `main` and link any related issue. If you cannot
build the PDFs, open a draft pull request and identify the outputs needing help.

## Reporting a resolution

When reporting a solution, follow the [resolution procedure](RESOLVED.md#recording-a-new-resolution):
retain the original ID and statement, explain exactly what is settled, and cite
the resolution. Do not increase the open count with solved problems, unsupported
claims, duplicate formulations or unverified candidates. Closing a GitHub issue
does not change mathematical status automatically.
