# Contributing

Use [GitHub issues](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues) for
new problem suggestions, missing references, rating feedback and status
corrections. A useful report identifies the problem ID, links a primary source,
and gives a theorem, conjecture or page locator. Use the correction-or-resolution template
when a question may have been resolved.

For a new problem, supply a precise statement, assumptions and quantifiers, its
numerical-linear-algebra connection, proposed difficulty and impact with a short
rationale, and evidence about later solutions. Check for equivalent entries
before proposing another ID. A research direction without a definite completion
criterion needs clarification before admission.

For your first pull request, fork the repository and create a branch. Add the new problem at `category/ID/README.md`, using a neighboring entry as a model. Include `Difficulty`, `Importance`, `Rating rationale`, `Status` and `Last checked`. Propose an unused ID; never recycle a published one. For an existing entry, edit its `README.md`, which is the source of truth.
Keep the mathematical target faithful to its source and distinguish a theorem
from a conjecture or a preprint claim. Use the [rating rubric](README.md#ratings)
and [status definitions](README.md#problem-status). Ratings assess the surviving
open question; historical ratings on resolved entries are explicitly identified.

Run `python3 tools/update_catalog.py` after changing a title, rating or status.
Run `python3 tools/render_problems.py ID` after editing a problem, using Pandoc
and XeLaTeX, and inspect its PDF. Include the Markdown, TeX and PDF changes
together. The renderer supports `PANDOC` and `XELATEX` executable overrides. Open the pull request against `main` and link any related issue. If you cannot build the PDFs, open a draft pull request and identify the outputs needing help.

When reporting a solution, follow the [resolution procedure](RESOLVED.md#recording-a-new-resolution):
retain the original ID and statement, explain exactly what is settled, and cite
the resolution. Do not increase the open count with solved problems, unsupported
claims, duplicate formulations or unverified candidates. Closing a GitHub issue
does not change mathematical status automatically.
