# Open Problems in Numerical Linear Algebra

A collection of precise open problems drawn from books and research
publications, with references and dated checks for subsequent solutions.

**Current collection: 159 / 1,000 problems. The project is incomplete.**

**[Browse all 159 problems →](CATALOG.md)**

## Browse by category

| Category | Problems |
| --- | ---: |
| [Linear systems and elimination](linear-systems-and-elimination/README.md) | 19 |
| [Eigenvalues and inverse problems](eigenvalues-and-inverse-problems/README.md) | 20 |
| [Matrix functions and stability](matrix-functions-and-stability/README.md) | 19 |
| [Randomized and low-rank approximation](randomized-and-low-rank-approximation/README.md) | 25 |
| [Tensor computations](tensor-computations/README.md) | 15 |
| [Nonnegative and positive factorizations](nonnegative-and-positive-factorizations/README.md) | 12 |
| [Matrix inequalities and norms](matrix-inequalities-and-norms/README.md) | 17 |
| [Frames and matrix designs](frames-and-matrix-designs/README.md) | 10 |
| [Matrix discrepancy and optimization](matrix-discrepancy-and-optimization/README.md) | 6 |
| [Arithmetic and complexity](arithmetic-and-complexity/README.md) | 11 |
| [Intervals and absolute value equations](intervals-and-absolute-value-equations/README.md) | 5 |

Open a category, then a problem folder. Every problem has three files:

- **`README.md`** — the canonical statement, rendered directly on GitHub and readable by chatbots.
- **`problem.pdf`** — a typeset document for reading, downloading, or printing.
- **`problem.tex`** — standalone LaTeX source for the PDF.

Shared definitions are included in each problem so it can be read independently. Problem IDs remain stable across the new categories.

Each problem gives its assumptions and quantifiers, one difficulty label, one
importance rating, a brief set of references, and a literature-status check.
The collection includes core NLA and directly relevant matrix theory and
computational complexity. Entries explain that connection where it is less
immediate. No solutions or proof attempts are part of this project.

The [wider literature screen](proof/WIDE-SEARCH-2026-09.md) adds 50 distinct problems from six searches, with source checks, partial results, exclusions, and uncounted leads. The earlier [Higham 2002 screen](proof/HIGHAM-2002-SCREEN.md) records three additions from the book.

## Ratings

Ratings are provisional editorial judgments. They describe the mathematical
scope and expected difficulty, rather than estimating a completion time.

| Difficulty | Meaning |
| --- | --- |
| **hard** | A focused unresolved question requiring substantial technical work within an established setting. |
| **challenging** | A substantial obstruction, new analysis, or new algorithm appears necessary; the statement spans a meaningful class of inputs. |
| **extreme** | A foundational or very general question with major theoretical obstacles, or a longstanding barrier at the frontier of the subject. |

| Importance | Meaning |
| --- | --- |
| **interesting to specialist** | Primarily advances a specific method, matrix class, or technical subfield. |
| **interesting to the community** | Relevant to a substantial part of the NLA community or to several numerical methods. |
| **broadly interesting** | Consequences extend across NLA and into other major areas of mathematics, computation, or applications. |

## What “open” means here

The latest screening date is **2026-09-08**. A historical open-problem citation
is checked against subsequent publications and targeted searches. The entry
records what was checked and distinguishes known special cases from the
remaining question. A search that finds no resolution cannot guarantee that
none exists, especially for older or less widely indexed sources.

Resolved questions, recent full-solution claims, and candidates with unclear
statements or status are kept outside the count. See [source coverage and
uncounted leads](proof/SOURCES.md) and the preserved [chapter screening notes](proof/catalog/README.md).
Clearly identified quantitative restatements are editorial formulations of
published questions, rather than quotations attributed to their authors.

The [canonical objective](PROBLEM.md) preserves the target of 1,000 distinct
entries. [Progress](PROGRESS.md) records actual coverage and outstanding work.
Suggestions and corrections should identify the problem ID and a primary
reference, particularly when reporting a solution or a missing assumption.

The [additional-problems screen](proof/ADDITIONAL-PROBLEMS-SCREEN.md) maps all 43 supplied candidates: 22 new entries, 15 duplicates, one grouped stronger formulation, and five withheld or excluded candidates.

The [further literature expansion](proof/LITERATURE-EXPANSION-2026-09.md) adds 12 problems on iterative methods, spectral perturbation, matrix equations, randomized approximation, and tensor energy computations, with precise source locators and later-status checks.

## Editing and PDF generation

Edit the problem’s `README.md`, which is the source of truth. With Pandoc and XeLaTeX installed, run `python3 tools/render_problems.py IE-02` to regenerate one problem, or omit the ID to regenerate the collection. Each exported `problem.tex` can also be compiled on its own with XeLaTeX. [The shared typesetting template](tools/problem-template.tex) controls appearance. Check the resulting PDF whenever a statement changes.
