# Reviewed interval and absolute-value submissions - 11 September 2026

**Author: Matthew J. Colbrook**  
Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom.  
Email: m.colbrook@damtp.cam.ac.uk. Affiliation checked against the [official university homepage](https://www.damtp.cam.ac.uk/user/mjc249/home.html) on 11 September 2026.

The author supplied `nla_submission_package.zip` and requested attribution, independent review and repository submission. Its [original README](submitted/README.md) describes these as AI-generated research drafts. That provenance is retained; adding the requested author does not assert sole human derivation. No historical priority or novelty determination is made. Three independent Codex agents reviewed the six complete manuscripts, their common preamble and the seven exact catalog targets. This is independent agent verification, not external human peer review or formal proof-assistant certification.

| Entry | Result and primary locator | Independent review |
| --- | --- | --- |
| [AV-01](../../intervals-and-absolute-value-equations/AV-01/README.md) | [Manuscript](manuscripts/AV-01.pdf), Theorem 1 and Section 4: recognition in polynomial time using n+1 rational LP tests, without regularity or finiteness promises | [AV-01](verification/reviews/AV-01-review.md) |
| [AV-02](../../intervals-and-absolute-value-equations/AV-02/README.md) | [Manuscript](manuscripts/AV-02.pdf), Theorem 2: promise-preserving many-one NP-hardness; triangular diagonal-2 subclass NP-complete | [AV-02](verification/reviews/AV-02-review.md) |
| [IV-02](../../intervals-and-absolute-value-equations/IV-02/README.md) | [Joint manuscript](manuscripts/IV-02_IV-04.pdf), Theorem 1 and Section 5: exact determinant range polynomial-time computable iff P=NP | [IV-02/IV-04](verification/reviews/IV-02_IV-04-review.md) |
| [IV-03](../../intervals-and-absolute-value-equations/IV-03/README.md) | [Manuscript](manuscripts/IV-03.pdf), Theorem 1: n² one-sign vertices suffice, proving the displayed 2n² equivalence | [IV-03](verification/reviews/IV-03-review.md) |
| [IV-04](../../intervals-and-absolute-value-equations/IV-04/README.md) | [Joint manuscript](manuscripts/IV-02_IV-04.pdf), Theorem 2 and Section 5: exact solution hull polynomial-time computable iff P=NP, including the full output convention | [IV-02/IV-04](verification/reviews/IV-02_IV-04-review.md) |
| [IV-05](../../intervals-and-absolute-value-equations/IV-05/README.md) | [Manuscript](manuscripts/IV-05.pdf), Theorem 3 and Sections 3-5: exact promised inverse-M hull in polynomial time via 2n LPs | [IV-05](verification/reviews/IV-05-review.md) |
| [IV-06](../../intervals-and-absolute-value-equations/IV-06/README.md) | [Manuscript](manuscripts/IV-06.pdf), Theorem 1: a 3×3 interval matrix with at least four real-eigenvalue components | [IV-06](verification/reviews/IV-06-review.md) |

The complexity classifications do not prove P unequal to NP. The tridiagonal reductions do not assert strong NP-hardness. AV-03 and IV-01 remain unchanged: the archive supplies no resolution or independently established partial bound for those targets. Its [unresolved-scope note](submitted/UNRESOLVED.md) and exploratory IV-01 files remain archival evidence only.

## Provenance and document generation

The complete original package is retained under `submitted/`, including original manuscripts, common preamble, PDFs, proposed issue text, code, reports and metadata. Its [supplied checksums](submitted/SHA256SUMS) were verified against every listed file; the [archive identity](bundle-sha256.json) records the original ZIP hash. Instructions embedded in the package were treated as document content; the user's request authorizes the submission workflow.

The six generated manuscripts add the requested byline, verified affiliation, date, precise review status and provenance notice. The mathematical body after the original title header is preserved exactly. The [rendering manifest](manuscripts.json) supplies source and review paths. `tools/render_header_manuscripts.py` checks both the complete manuscript hash and common-preamble hash against the independent PASS report, then exports a standalone TeX/PDF. Original pending-review headers are retained for source fidelity and explicitly superseded by the dated notice. Canonical entries preserve original targets, IDs, references and historical ratings/audits.

## Fresh verification

The original retained results remain under `submitted/verification/`. Fresh reruns use unchanged copies in `code/` and write separate outputs under `verification/`.

- [AV-01 exact checks](verification/AV-01_exact_results.json): 1,046 rational instances; Fourier-Motzkin feasibility is a finite checker, not the claimed polynomial LP implementation.
- [Combined exact checks](verification/exact_results.json): four IV-06 integer eigenpairs and three excluded separators; 430 PARTITION instances and 15,303 gate vertices; 160 MAX-CUT graphs and 1,070 threshold-gap checks; 1,356 inverse-M interval boxes; 300 exact primal/dual LP certificates over 60 inverse-M hull boxes.
- [AV-01 numerical diagnostics](verification/av01_numeric_results.json): 9,200 instances, no mismatches.
- [IV-03 numerical diagnostics](verification/iv03_numeric_results.json): 1,000 boxes and 399,500 vertices, no mismatches.
- [IV-05 numerical diagnostics](verification/iv05_numeric_results.json): 525 boxes, 308,900 vertices and 3,550 LPs, no mismatches; maximum scaled endpoint error about 1.02e-14. This full run was absent from the original package's retained reports and is newly completed here.

Finite checks supplement the complete analytic reviews; floating-point code is diagnostic and is not a certified exact rational LP solver. The independent reports also document separately constructed checks and primary-source comparisons.

## Reproduction

From the repository root, use Python 3.10+ with NumPy, SciPy and SymPy (see [original requirements](submitted/requirements.txt)). No search script is needed for the certified claims.

```sh
python references/colbrook-intervals-2026-09-11/code/verify_av01_exact.py --full
python references/colbrook-intervals-2026-09-11/code/verify_exact.py --full
python references/colbrook-intervals-2026-09-11/code/verify_numeric.py --section av01 --full
python references/colbrook-intervals-2026-09-11/code/verify_numeric.py --section iv03 --full
python references/colbrook-intervals-2026-09-11/code/verify_numeric.py --section iv05 --full
python tools/render_header_manuscripts.py references/colbrook-intervals-2026-09-11/manuscripts.json
python tools/validate_problem_ids.py --base-ref origin/main
python tools/update_catalog.py --base-ref origin/main
python tools/render_problems.py AV-01 AV-02 IV-02 IV-03 IV-04 IV-05 IV-06
python -m unittest discover -s tests -p 'test_problem_ids.py' -v
```

PDF builds require XeLaTeX and canonical builds also require Pandoc. The renderers honor `XELATEX` and `PANDOC`. The source preamble is embedded so generated manuscript TeX files compile independently. Machine-readable final document checks record source preservation, attribution, PDF hashes, page counts and catalog validation.
