# Five proposed resolutions submitted by Matthew Colbrook

Submission date: **11 September 2026**. The supplied manuscripts target repository
snapshot `b4123194697bdf6f8f82518c1dd7d6c40a30c2e0`, which matched upstream `main`
when this contribution was prepared.

The status proposed for all five entries is **Solution claimed**. Their complete
manuscripts disclose generation in a ChatGPT conversation and are included
without changes to their Markdown, standalone LaTeX or PDF files. Matthew
Colbrook is identified as the submitter; no independent referee report,
publication, priority claim or formal proof certificate is asserted.

| ID | Claimed outcome | Complete manuscript and precise locator |
| --- | --- | --- |
| [IS-02](../../eigenvalues-and-inverse-problems/IS-02/README.md) | Negative: a spectrally unique order-four matrix outside the proposed locus. | [Theorem IS-02, sections 1–2](../../eigenvalues-and-inverse-problems/IS-02/solution.md) · [PDF](../../eigenvalues-and-inverse-problems/IS-02/solution.pdf) |
| [SP-04](../../eigenvalues-and-inverse-problems/SP-04/README.md) | Negative: the least-absolute-multiplier rule fails on an open set of real order-three data. | [Theorem SP-04, sections 1–4](../../eigenvalues-and-inverse-problems/SP-04/solution.md) · [PDF](../../eigenvalues-and-inverse-problems/SP-04/solution.pdf) |
| [SP-05](../../eigenvalues-and-inverse-problems/SP-05/README.md) | Affirmative: a positive-semidefinite minimizing eigenmatrix for every real positive definite pair. | [Theorem SP-05, sections 1–3](../../eigenvalues-and-inverse-problems/SP-05/solution.md) · [PDF](../../eigenvalues-and-inverse-problems/SP-05/solution.pdf) |
| [KE-04](../../eigenvalues-and-inverse-problems/KE-04/README.md) | Affirmative: strict interval occupancy at all allowed later block Lanczos iterations. | [Theorem KE-04, sections 1–3](../../eigenvalues-and-inverse-problems/KE-04/solution.md) · [PDF](../../eigenvalues-and-inverse-problems/KE-04/solution.pdf) |
| [KE-03](../../eigenvalues-and-inverse-problems/KE-03/README.md) | Affirmative in the displayed exact-query model: logarithmic dimension dependence. | [Theorem KE-03, sections 1–5](../../eigenvalues-and-inverse-problems/KE-03/solution.md) · [PDF](../../eigenvalues-and-inverse-problems/KE-03/solution.pdf) |

## Scope of the checks

The submission preparation compared each manuscript's hypotheses, quantifiers
and claimed conclusion with its canonical entry. The original problem statements,
references and earlier audit notes are retained. No new exhaustive literature
search or independent mathematical proof audit was performed.

All 35 checksums listed in the supplied bundle were verified before copying the
files. The [supporting script](verification/check_results.py) was inspected and
rerun successfully on 11 September 2026 using NumPy 2.5.0, SciPy 1.18.0 and
SymPy 1.14.0. Its diagnostic output matched the supplied
[recorded results](verification/rerun-results.txt). The original
[environment requirements](verification/requirements.txt) and
[diagnostic notes](verification/README.md) are preserved alongside it.

The checks cover the exact IS-02 identities, rational SP-04 bounds and numerical
stationary values, 84 SP-05 positive definite pairs, 2,800 KE-04 intervals and
400 KE-03 shift-geometry cases. These checks support the submission but do not
establish the universal claims. In particular, the KE-03 diagnostics do not
implement the complete exact-query algorithm or establish floating-point
stability or a total-runtime bound.

## Repository documents checked

The five canonical problem documents were regenerated with Pandoc 3.11 and
XeLaTeX from TeX Live 2023. Each resulting problem PDF has two pages, with no
reported overfull boxes or missing characters. All 10 final problem pages and
all 13 supplied manuscript pages were visually inspected; extracted text was
also checked against page bounds. The renderer's existing reference-page
settings were extended to keep the new claim notices from leaving isolated
audit paragraphs on otherwise empty pages.

Regenerating the indexes a second time produced identical files. The resulting
catalog has 195 open targets (109 open and 86 partially resolved), six solution
claims and one solved entry. All original statement text and all 15 supplied
manuscript files were checked for preservation, and relative file links in the
changed documentation were checked for existing targets.
