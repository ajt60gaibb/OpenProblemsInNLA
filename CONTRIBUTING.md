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

For your first pull request, fork the repository and create a branch. Add the new problem at `category/ID/README.md`, using a neighboring entry as a model. Include `Difficulty`, `Importance`, `Rating rationale`, `Status` and `Last checked`. Register a new ID as described below. For an existing entry, edit its `README.md`, which is the source of truth.
Keep the mathematical target faithful to its source and distinguish a theorem
from a conjecture or a preprint claim. Use the [rating rubric](README.md#ratings)
and [status definitions](README.md#problem-status). Ratings assess the surviving
open question; historical ratings on resolved entries are explicitly identified.

## Mathematics in GitHub descriptions

Use protected inline math, for example ``$`\|A\|_2`$``, so Markdown preserves
norm bars, set braces and matrix row separators. Put display equations in
fenced `math` blocks, separated from surrounding prose by blank lines:

````markdown
```math
\|A\|_2 = \max_{\|x\|_2=1}\|Ax\|_2.
```
````

GitHub currently rejects `\operatorname`. Use
`\mathop{\mathrm{rank}}\nolimits ` for the same operator spacing and script
placement; keep a space after `\nolimits` before an alphabetic argument.
Write `x< y` with a space after `<` before a letter: GitHub can otherwise
interpret the rest of a displayed formula as an HTML tag.

For an equation inside a list, use a separate indented paragraph containing
protected inline math beginning with `\displaystyle`, for example
``$`\displaystyle \|A\|_2 \le 1.`$``. GitHub currently leaves indented
`math` fences as literal code. The PDF renderer restores these standalone
paragraphs as display equations.

The [GitHub math documentation](https://docs.github.com/en/get-started/writing-on-github/working-with-advanced-formatting/writing-mathematical-expressions)
describes the protected delimiters and fenced blocks.

Run `python3 tools/format_math.py --write IE-02` to normalize an entry, then
review its diff. `python3 tools/format_math.py --check` checks every registered
description and also runs in CI. Keep PDF layout commands in the renderer.
The PDF renderer accepts this GitHub notation as mathematics.

## Permanent problem IDs

Every published ID and its canonical README path are permanent. Never renumber,
compact, recycle, or reassign them, even after a solution or category-listing
change. Retain the original target and resolution on solved pages. For a
withdrawal, retain the page as a tombstone with `Status: Withdrawn`, the original
target, metadata and a dated explanation. Status changes affect the open count,
not problem numbering. Replacing an existing target with an unrelated problem
is also prohibited; this requires content review beyond automated ID checks.

For a new entry, inspect [problem_ids.json](problem_ids.json), choose the next
number above the largest registered number with that prefix, and explicitly
append the ID/path pair to that JSON object, such as
`"RA-18": "randomized-and-low-rank-approximation/RA-18/README.md"`.
Never fill a numerical gap. Use at least two digits (`RA-01`, `RA-100`). Keep
all existing registry mappings. Coordinate competing submissions for the same
new number before merging.

Run `python3 tools/validate_problem_ids.py --base-ref origin/main` against the
published branch before submitting. CI compares the registry and canonical
pages with the published default branch and also the pull request base or
previous pushed commit when available, including protection on new branches.
The first registry
introduction also protects entries already present in that base tree. The
validator checks HEAD by default in a git checkout; extracted source archives
can only validate their current files without an explicit historical ref.

## Updating indexes and PDFs

The build tools require Python 3; PDF generation also requires Pandoc and XeLaTeX.
After editing an entry, update the indexes and regenerate its documents:

```bash
python3 tools/update_catalog.py --base-ref origin/main
python3 tools/render_problems.py IE-02
```

Replace `IE-02` with the changed problem's ID; several IDs may be supplied.
Omit the IDs to render the whole collection. The index tool rebuilds `CATALOG.md`,
category indexes and the README counts from canonical metadata, excluding solved,
Lean-verified, claimed and unverified entries from the open count.
Withdrawn entries are retained outside that count as well. The index tool
validates permanent IDs before writing any generated file. Run the safeguard
tests with `python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v`.

Inspect the resulting PDF and include the Markdown, TeX and PDF changes together.
For changes limited to Markdown delimiters or equivalent operator typography,
retain the existing TeX/PDF when their mathematical content is unchanged and
verify the renderer's math conversion instead. Changes to content or PDF layout
still require regeneration and visual inspection.
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

## Lean verification

Use `**Status:** Lean verified` only for a complete resolution of the original
target with reviewed Lean verification evidence. `Solved` remains appropriate
for a published result or a complete argument that has passed an independent
informal audit, including an AI-agent audit. Record who or what performed that
audit and link the report; finding no mistake does not establish formal
verification or external human peer review.

For promotion to `Lean verified`, add a **Lean proof and verification evidence**
section to the canonical README containing:

1. A stable link to the proof source at an immutable revision, the Lean
   toolchain version, and pinned dependency versions (including mathlib when
   used).
2. The exact theorem declaration names and a comparison of their definitions,
   assumptions, quantifiers and conclusions with the original problem. All
   premises needed to settle the target must be proved or be assumptions
   already present in that target.
3. Reproduction commands and a dated successful verification log covering
   those declarations and their dependencies. State whether this catalog
   reran the checks or reviewed a public verification record; do not imply a
   local rerun when none occurred.
4. A transitive axiom report (for example, `#print axioms` for every target
   theorem). Accept only Lean's standard foundational axioms `propext`,
   `Classical.choice` and `Quot.sound`, or a subset. No `sorryAx`, unproved
   custom axioms, or additional trust in native execution may support the
   target theorem. A build succeeding on its own is insufficient evidence.

Lean's documentation explains [proof validation and statement matching](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
and [transitive axiom checks](https://lean-lang.org/doc/reference/latest/Axioms/).

Link this evidence from the resolution notice and [resolution archive](RESOLVED.md).
A public source and log may support the status after review; merely mentioning
a Lean formalization does not. If a source revision changes, recheck the
correspondence and verification evidence before attaching the status to it.
Lean verification of a special case, a conditional reduction or supporting
lemmas does not promote the whole problem: retain `Partially resolved` (or
`Solved` if a complete informal resolution exists) and describe the formalized
scope. Keep all IDs, paths and original targets unchanged.
