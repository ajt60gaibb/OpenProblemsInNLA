# Factorization submissions by Matthew J. Colbrook

**Author:** Matthew J. Colbrook. **Date:** 11 September 2026.  
**Affiliation:** Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom. **Email:** m.colbrook@damtp.cam.ac.uk. Checked against the [official Cambridge homepage](https://www.damtp.cam.ac.uk/user/mjc249/home.html).

This new batch contains seven manuscripts. Five complete catalog targets receive independent PASS reviews: NM-03, NM-04, NR-04, PF-02 and PF-05. NR-03 and PF-01 receive verified partial results, with their remaining infinite families explicitly retained. Three separate Codex agents read and independently checked the complete proofs, assumptions, quantifiers, boundary cases and primary-source alignment; seven detailed reports record the resulting scopes. The user supplied the manuscripts and requested the Matthew J. Colbrook author byline on all seven final exports.

| Entry | Proposed status | Primary manuscript locator | Independent review |
| --- | --- | --- | --- |
| [NM-03](../../nonnegative-and-positive-factorizations/NM-03/README.md) | Solved | [Theorem 1; Theorem 5 and Corollary 6 strengthen the construction](manuscripts/NM-03_rank_two_approximation_hardness.pdf) | [PASS](verification/reviews/NM-03-review.md) |
| [NM-04](../../nonnegative-and-positive-factorizations/NM-04/README.md) | Solved | [Theorem 1](manuscripts/NM-04_sinkhorn_identity.pdf) | [PASS](verification/reviews/NM-04-review.md) |
| [NR-03](../../nonnegative-and-positive-factorizations/NR-03/README.md) | Partially resolved | [Theorem 1 and Lemma 2](manuscripts/NR-03_n3_exact_rank.pdf) | [PASS](verification/reviews/NR-03-review.md) |
| [NR-04](../../nonnegative-and-positive-factorizations/NR-04/README.md) | Solved | [Theorem 1, with Theorem 4 for the lower bound](manuscripts/NR-04_nine_point_distance.pdf) | [PASS](verification/reviews/NR-04-review.md) |
| [PF-01](../../nonnegative-and-positive-factorizations/PF-01/README.md) | Partially resolved | [Theorem 1, Corollary 5 and equation (8)](manuscripts/PF-01_subset_intersection.pdf) | [PASS](verification/reviews/PF-01-review.md) |
| [PF-02](../../nonnegative-and-positive-factorizations/PF-02/README.md) | Solved | [Theorem 1; Theorem 4 extends the counterexamples to every factor size](manuscripts/PF-02_disconnected_orbits.pdf) | [PASS](verification/reviews/PF-02-review.md) |
| [PF-05](../../nonnegative-and-positive-factorizations/PF-05/README.md) | Solved | [Theorem 1, with Theorem 8 for the zero-entry construction](manuscripts/PF-05_rigidity_with_zeros.pdf) | [PASS](verification/reviews/PF-05-review.md) |

## Exact scopes

**NM-03.** The exact rational-input decision problem is NP-hard under polynomial-time many-one reductions, even for strictly positive symmetric positive-definite inputs. The proof supplies an inverse-polynomial additive squared-error gap and a polynomial-time rational perturbation to simple spectrum. Factors may be real, exactly as in the canonical question. NP membership and constant-relative-error hardness are not asserted. 

**NM-04.** The complete Rowland--Wu coefficient identity holds for every positive real rectangular matrix and all $m,n\ge1$. The proof identifies the coefficient sum with one determinant and constructs a null vector after scaling. Vanishing minors and the cases $m=1$ or $n=1$ are included. This proves the displayed coefficients, beyond the previously known algebraic-degree bound. 

**NR-03.** The fixed three-bit quadratic correlation matrix has nonnegative rank exactly eight. Its ordinary-rank-seven parity null vector constrains both factors in a hypothetical seven-term factorization; nine distinguished entries then exclude such a factorization. The full prescribed-completion conjecture for every $n\ge4$ remains unresolved. The parity restriction is proved only for a hypothetical factorization whose inner dimension equals ordinary rank; it is not imposed on arbitrary wider factorizations.

**NR-04.** The nine-point matrix $D_{ij}=(i-j)^2$ has nonnegative rank seven, so no exact six-term nonnegative factorization exists. A polygon-contact argument applied to both factors, together with Sylvester's rank inequality, proves the lower bound; an explicit seven-term integer factorization proves the upper bound. 

**PF-01.** The real positive semidefinite rank is exactly four for $n=5$ and $n=6$. Explicit graph factors give the general bound $\operatorname{rank}_{\rm psd}M^{(n)}\le\lceil2\sqrt{2\lfloor(n-1)/2\rfloor}\rceil$, and submatrix monotonicity gives a lower bound of four for every $n\ge5$. The exact ranks as a function of $n$ remain undetermined for $n\ge7$. In particular, the new upper bound five at $n=7,8$ is not accompanied by a matching lower bound five. The finite orders remain part of this single family entry.

**PF-02.** A strictly positive integer $6\times6$ matrix has ordinary rank six and real positive semidefinite rank three, while its minimal-factor congruence quotient is disconnected. A continuous congruence-invariant orientation takes opposite signs on two explicit factorizations, proving actual disconnectedness in the required quotient topology. Further constructions cover every factor size $k\ge3$, including strictly positive rational examples by a nonquantitative perturbation argument. 

**PF-05.** For every real size-two positive semidefinite factorization of an ordinary-rank-three matrix, feasible straight-line infinitesimal rigidity is equivalent to uniqueness up to congruence. The zero-entry argument handles repeated or singular factors and zero rows and columns; the cited positive-entry theorem covers the remaining case. The feasible directions and equivalence group agree exactly with the canonical definitions. 

## Verification and provenance

The [archive manifest](bundle-sha256.json) records the supplied zip and every contained file by SHA-256, computed on receipt. The original standalone TeX manuscripts, README and requirements are retained under [original](original). The input contained no result files; [results](results) contains the new diagnostic runs. Original supplied PDF identities are recorded in the manifest; the final PDFs are regenerated from the reviewed TeX rather than opaque replacements.

The [reviewed sources](reviewed-sources) preserve all mathematical arguments. NR-04 has three local clarifications: its contact lemma explicitly says convex polygons for P and R, as already required by its proof and guaranteed in every application, and the Gillis--Glineur Theorem 8 bibliography locator is corrected to Section 4.2.1. Its independent review rechecked the changes and records original and revised complete hashes. Every other reviewed source equals the supplied TeX. The renderer adds author, affiliation, date and a verification notice while preserving the complete reviewed body after the title command. Each export includes its own preamble and bibliography.

The known reflection upper-bound construction for NR-04 is not claimed as new; the benchmark source credits Hrubeš. The PF-01 size-four upper bound at order five was already known; the manuscript supplies explicit factors and the matching lower bound. The PF-05 proof uses the prior positive-entry theorem for that case and proves the zero-entry extension. Further attribution and source comparisons are in the individual reviews. No exhaustive novelty search, priority certification, journal acceptance or formal proof-assistant verification is claimed. Independent agent proof review is distinct from the finite diagnostic checks.

## Reproduction

The eleven inspected `verify_*.py` scripts use SymPy 1.14.0 and exact integer/rational or symbolic arithmetic. All eleven were rerun successfully. They include finite certificates for the complexity reduction, both factor ranks, all 400 order-six trace products, exact Hessian obstructions, zero-factor identities, and a degree-20 Kruithof polynomial with its irreducibility and printed coefficients checked. General theorem validity rests on the analytic reviews, not those finite examples. In PF-02, the sample perturbation eta=1/100 tests the explicit factors; it does not certify the nonquantitative uniform component-separation threshold.

From the repository root, install the versions in [requirements](verification/requirements.txt), then run each script in [verification](verification). Keep the companion scripts together; they write into the sibling results directory. Regenerate the documents and indexes with:

```text
python -B tools/render_reviewed_tex.py references/colbrook-factorization-2026-09-11/manuscripts.json
python -B tools/update_catalog.py
python -B tools/render_problems.py NM-03 NM-04 NR-03 NR-04 PF-01 PF-02 PF-05
```

Pandoc and XeLaTeX are required; `PANDOC` and `XELATEX` may name their executables. The source hash in each generated TeX and explicit body markers support identity checks. Original canonical IDs, mathematical statements, references and prior audits remain intact. This contribution is based directly on upstream main and is a separate pull request from PR #6 and PR #32; maintainer review and merge into main are requested.

## Final document checks

The [machine-readable check record](verification/document-checks.json) records the SHA-256 and page count of all fourteen final PDFs, the eleven successful diagnostic runs, source/body identity, original catalog preservation, author metadata and local-link checks. All 49 final pages were visually inspected; the fourteen documents compiled without layout or reference warnings. Regenerating the catalog a second time made no changes. This branch contains 202 entries: 110 Open, 85 Partially resolved, one Solution claimed and six Solved, giving 195 entries in the open count.
