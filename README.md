# Open Problems in Numerical Linear Algebra

A collection of precise open problems drawn from books and research
publications, with references and dated checks for subsequent solutions.

I have several motivations for starting this repository: 
1. We are a few weeks away from an AI company or undergraduates or hobbyists from looping over our literature and solving many of our precise conjectures, without much understanding. I would like our community to solve them first and digest the consequences. 
2. I would like to show the community that most of our precise conjectures can now be solved by the best AI models on the market. I am mourning just like you are.  
3. I would like to collect the solutions in one place because they are coming in fast.

If one of your favorite open problems is solved here, we strongly encourage you to improve the proof, write about it, and publish it. We only have three hopes: (1) You will reference this GitHub repository as the original proof source (see below), (2) Add your preprint to the repository, and (3) Update any information about the problem in the repository. 

<!-- catalog-summary -->
**111 problems with open targets:** 41 open and 70 partially resolved. **106 other retained entries**, excluded from the open count.

**Resolution evidence:** 48 solved (published or independently audited); 58 solved with Lean verification.

Each entry records its own literature-check date. Literature checks are bounded; ratings are editorial. “Impact” uses the canonical `Importance` field.

**[Browse all 111 open targets →](CATALOG.md)** · **[Solved and claimed solutions →](RESOLVED.md)**
<!-- /catalog-summary -->

## Special thanks

Special thanks to **George Stepaniants**, **Matthew J. Colbrook**, and **Sidney Holden** for their substantial contributions to this repository so far, and to everyone else who has contributed to the repository or emailed additions and corrections.

If you would like to get involved but don't know how, please email [townsend@cornell.edu](mailto:townsend@cornell.edu).

## Browse by category

| Category | Problems |
| --- | ---: |
| [Linear systems and elimination](linear-systems-and-elimination/README.md) | 9 |
| [Eigenvalues and inverse problems](eigenvalues-and-inverse-problems/README.md) | 13 |
| [Matrix functions and stability](matrix-functions-and-stability/README.md) | 11 |
| [Randomized and low-rank approximation](randomized-and-low-rank-approximation/README.md) | 12 |
| [Tensor computations](tensor-computations/README.md) | 17 |
| [Nonnegative and positive factorizations](nonnegative-and-positive-factorizations/README.md) | 4 |
| [Matrix inequalities and norms](matrix-inequalities-and-norms/README.md) | 16 |
| [Frames and matrix designs](frames-and-matrix-designs/README.md) | 11 |
| [Matrix discrepancy and optimization](matrix-discrepancy-and-optimization/README.md) | 3 |
| [Arithmetic and complexity](arithmetic-and-complexity/README.md) | 13 |
| [Intervals and absolute value equations](intervals-and-absolute-value-equations/README.md) | 2 |

Open a category, then a problem folder. Every problem has three files:

- **`README.md`** — the canonical statement, rendered directly on GitHub.
- **`problem.pdf`** — a typeset document for reading, downloading, or printing.
- **`problem.tex`** — standalone LaTeX source for the PDF.

Shared definitions are included in each problem so it can be read independently.
**Published problem numbers are permanent.** Solving or withdrawing a problem
changes its status and the open-problem count, never its ID. We retain its
original statement and canonical page, including when category listings change.
The append-only [ID registry](problem_ids.json) and automated checks prevent
renumbering, removal, path reassignment, and reuse; new IDs extend their prefix's
numbering without filling gaps. See [the contribution rules](CONTRIBUTING.md#permanent-problem-ids).

Each problem gives its assumptions and quantifiers, one difficulty label, one
importance rating, a brief set of references, and a literature-status check.
The collection includes core NLA and directly relevant matrix theory and
computational complexity. Entries explain that connection where it is less
immediate. Resolution arguments are recorded with their verification level;
[MI-13](matrix-inequalities-and-norms/MI-13/README.md) includes a complete proof.

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

## Problem status

Status is separate from difficulty and impact and appears on every problem,
PDF and index row. A solved problem keeps its ID and original statement; its
page records the outcome, date and exact resolution reference.

| Display | Meaning | Counted as open? |
| --- | --- | --- |
| 🔵 **OPEN** | The stated target remains unresolved in the checked literature. | Yes |
| 🟡 **PARTIAL** | Substantive cases inside the displayed target are proved; the entry identifies the remaining cases. This may reflect older results, not necessarily a new discovery. | Yes, once |
| 🟠 **SOLUTION CLAIMED** | A primary manuscript claims a complete resolution; its full proof has not been independently verified here. | No |
| ✅ **SOLVED** | A published result or an independently audited argument settles the exact target, affirmatively or by a counterexample. An AI-agent audit can support this status; it does not establish formal verification. | No |
| 🏆 **LEAN VERIFIED** | A Lean proof of the exact target has passed kernel checking, with reviewed statement correspondence and a reproducible verification record. This is the formal-verification level above Solved. | No |
| ⚪ **NEEDS VERIFICATION** | A material statement or status issue prevents admission. This is not a claim that the problem is solved. | No |
| ⚫ **WITHDRAWN** | A retained original entry explains why it was withdrawn; its ID and canonical page remain reserved. | No |

For complete resolutions, the evidence levels are **Solution claimed → Solved →
Lean verified**. An agent finding no error is an informal audit, not a proof
certificate or external human peer review. Each resolution records the kind
and scope of review actually performed. `Solved` alone makes no claim of Lean
verification; promotion requires the [Lean evidence requirements](CONTRIBUTING.md#lean-verification).
A Lean proof of only a special case does not promote the whole problem; if
cases remain open, its status stays `Partially resolved`.
Lean checks the formal statement; its correspondence to the original
mathematical target still requires review.

We retain older-source entries when the exact question is supported and no
resolution was found, but explicitly flag the limits of that evidence. An
improved bound or a result for a different algorithm or model is not a full
resolution. See [solved problems and solution claims](RESOLVED.md) for the archive
and the procedure for reporting a solution.

## What “open” means here

The latest full-catalog audit date is **2026-09-10**. A historical open-problem citation
is checked against subsequent publications and targeted searches. The entry
records what was checked and distinguishes known special cases from the
remaining question. A search that finds no resolution cannot guarantee that
none exists, especially for older or less widely indexed sources.

Resolved questions, recent full-solution claims, and candidates with unclear
statements or status are kept outside the count. The [supporting references](references/README.md)
document source coverage, excluded candidates and the status audit.
Clearly identified quantitative restatements are editorial formulations of
published questions, rather than quotations attributed to their authors.

The [full status and rating audit](references/STATUS-AUDIT-2026-09-10.md) covers every entry present at that date.
Every pair of ratings has a short rationale.

## Contributing

Suggestions, references and corrections are welcome through [GitHub issues](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues) and pull requests. See [CONTRIBUTING.md](CONTRIBUTING.md) for admission criteria, editing and PDF generation, and the [correction or resolution template](.github/ISSUE_TEMPLATE/correction_or_resolution.md) for reporting a solution. A closed issue is not a mathematical status label; the canonical entry and indexes show whether a problem is solved.

## Citing this collection

If you use this collection, please cite:

```bibtex
@misc{townsend2026openproblemsnla,
  author = {Townsend, Alex},
  title  = {{Open Problems in Numerical Linear Algebra}},
  year   = {2026},
  url    = {https://github.com/ajt60gaibb/OpenProblemsInNLA},
  note   = {GitHub repository}
}
```

Include your access date or the commit used when referring to a particular version.
For an individual problem, give its ID and cite the original sources listed in the entry as well.
