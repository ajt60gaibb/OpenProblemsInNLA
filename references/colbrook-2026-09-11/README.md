# Five independently reviewed resolutions by Matthew J. Colbrook

**Author:** Matthew J. Colbrook.  
**Affiliation:** Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom.  
**Email:** m.colbrook@damtp.cam.ac.uk.  
**Submission and review date:** 11 September 2026.

The author byline is recorded at Matthew J. Colbrook's explicit request. The
current department, university and email were checked against his
[official Cambridge homepage](https://www.damtp.cam.ac.uk/user/mjc249/home.html)
on 11 September 2026.

## Independent proof verification

All five complete proofs received **PASS** verdicts from separate Codex review
agents working from the canonical targets and manuscripts. Three review agents
covered the five proofs, with one independent review per proof. They checked
mathematical derivations, assumptions, quantifiers and boundary cases; they did
not use the supplied numerical diagnostics as a substitute for proof review.
The repository status is **Solved**, with the verification level recorded.

| ID | Outcome | Manuscript locator | Independent review |
| --- | --- | --- | --- |
| [IS-02](../../eigenvalues-and-inverse-problems/IS-02/README.md) | Negative | [Theorem IS-02, sections 1–2](../../eigenvalues-and-inverse-problems/IS-02/solution.md) · [PDF](../../eigenvalues-and-inverse-problems/IS-02/solution.pdf) | [PASS report](verification/reviews/IS-02-review.md) |
| [SP-04](../../eigenvalues-and-inverse-problems/SP-04/README.md) | Negative | [Theorem SP-04, sections 1–4](../../eigenvalues-and-inverse-problems/SP-04/solution.md) · [PDF](../../eigenvalues-and-inverse-problems/SP-04/solution.pdf) | [PASS report](verification/reviews/SP-04-review.md) |
| [SP-05](../../eigenvalues-and-inverse-problems/SP-05/README.md) | Affirmative | [Theorem SP-05, sections 1–3](../../eigenvalues-and-inverse-problems/SP-05/solution.md) · [PDF](../../eigenvalues-and-inverse-problems/SP-05/solution.pdf) | [PASS report](verification/reviews/SP-05-review.md) |
| [KE-04](../../eigenvalues-and-inverse-problems/KE-04/README.md) | Affirmative | [Theorem KE-04, sections 1–3](../../eigenvalues-and-inverse-problems/KE-04/solution.md) · [PDF](../../eigenvalues-and-inverse-problems/KE-04/solution.pdf) | [PASS report](verification/reviews/KE-04-review.md) |
| [KE-03](../../eigenvalues-and-inverse-problems/KE-03/README.md) | Affirmative in the displayed exact-query model | [Theorem KE-03, sections 1–5](../../eigenvalues-and-inverse-problems/KE-03/solution.md) · [PDF](../../eigenvalues-and-inverse-problems/KE-03/solution.pdf) | [PASS report](verification/reviews/KE-03-review.md) |

Each report records a SHA-256 hash of the precise theorem-and-proof block it
reviewed. Those hashes were checked against the final Markdown. The proof
blocks are unchanged; the author metadata, verification notices and document
presentation have been updated. Original problem statements, references and
prior literature checks are preserved.

The original proof drafts were generated in a ChatGPT conversation. This
provenance remains disclosed. Independent Codex-agent verification is not
external human peer review or a formal machine-checked certificate. The
reviews assess correctness within the exact catalog targets; they do not
establish novelty or first-discovery priority. In particular, KE-03 bounds
exact forward-oracle query count, not total runtime, bit complexity or
floating-point error.

## Submission history

The [initial submission commit](https://github.com/MColbrook/OpenProblemsInNLA/commit/fe025e14d2639cbae59f98cacf4023d83addcb89)
recorded the five results as **Solution claimed**, attributed Matthew Colbrook
as submitter, and preserved all 15 supplied manuscript files byte for byte.
All 35 bundle checksums were verified at that stage. The original target
snapshot was `b4123194697bdf6f8f82518c1dd7d6c40a30c2e0`.

Later on 11 September, the author requested the named byline and independent
agent proof verification. All five reviews passed, supporting the change to
**Solved**. The original submissions and their prior status remain in Git
history. The open count remains 195: 109 open and 86 partially resolved. There
are now six solved entries and one remaining solution claim.

The five public review threads are [IS-02](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/1),
[SP-04](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/2),
[SP-05](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/3),
[KE-04](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/4), and
[KE-03](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/5).
The repository update is proposed in [pull request #6](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/6).

## Supporting diagnostics

The [supplied diagnostic script](verification/check_results.py) was inspected
and rerun successfully on 11 September using NumPy 2.5.0, SciPy 1.18.0 and
SymPy 1.14.0. Its output matched the [supplied results](verification/rerun-results.txt).
The original [requirements](verification/requirements.txt) and
[diagnostic notes](verification/README.md) are retained as the initial run record.

These checks cover the exact IS-02 identities, rational SP-04 bounds and
stationary values, 84 SP-05 positive definite pairs, 2,800 KE-04 intervals and
400 KE-03 shift-geometry cases. The independent mathematical reviews are
separate from these diagnostics. The KE-03 tests do not implement the complete
exact-query algorithm or establish numerical stability.

## Regenerating the documents

Canonical problem statements use `tools/render_problems.py`. The resolution
manuscripts use `tools/render_solutions.py` and the shared
`tools/solution-template.tex`; author, affiliation, email and review metadata
are maintained in each `solution.md`. Both renderers require Pandoc and XeLaTeX
and accept the `PANDOC` and `XELATEX` executable overrides.

```bash
python3 tools/update_catalog.py
python3 tools/render_problems.py IS-02 SP-04 SP-05 KE-04 KE-03
python3 tools/render_solutions.py IS-02 SP-04 SP-05 KE-04 KE-03
```

The submission builds use Pandoc 3.11 and XeLaTeX from TeX Live 2023. On Windows,
Python can be run with `-X utf8` for the existing index and problem renderers.

## Final document checks

All five authored manuscripts and five problem PDFs compiled without overfull-box
or missing-character warnings. Their 23 pages (13 manuscript pages and 10 problem
pages) were visually inspected, and extracted text was checked against page
bounds. Author bylines, affiliations, PDF author metadata and solved-status
notices were checked. All reviewed proof hashes match the final Markdown, the
original mathematical problem statements are unchanged, relative file links
resolve, and a second index regeneration produced identical files.
