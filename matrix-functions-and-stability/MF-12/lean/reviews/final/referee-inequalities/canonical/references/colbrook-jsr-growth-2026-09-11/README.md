# Three joint-spectral-radius and growth resolutions — 11 September 2026

**Author:** Matthew J. Colbrook.  
**Affiliation:** Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom.  
**Email:** m.colbrook@damtp.cam.ac.uk.  
**Submission and review date:** 11 September 2026.

The author attribution is recorded at the submitter's request. The affiliation and contact details were checked against the [official Cambridge homepage](https://www.damtp.cam.ac.uk/user/mjc249/home.html) on 11 September 2026. The supplied proofs were developed with AI assistance. Two separate Codex mathematical review agents checked the complete manuscripts, with one reviewer covering MF-05 and MF-07 and a second covering MF-12. A third agent independently reviewed the code and computational evidence. No external human peer review, formal proof certification or historical priority determination is claimed.

## Resolutions and exact scopes

| Canonical target | Complete authored manuscript | Independent mathematical review |
| --- | --- | --- |
| [MF-05](../../matrix-functions-and-stability/MF-05/README.md): Solved, affirmative | [PDF](manuscripts/uniform_growth_and_holder.pdf) · [TeX](manuscripts/uniform_growth_and_holder.tex), Theorem 2 and Corollary 7 | [PASS report](verification/reviews/MF-05-MF-07-review.md) |
| [MF-07](../../matrix-functions-and-stability/MF-07/README.md): Solved, affirmative | [PDF](manuscripts/uniform_growth_and_holder.pdf) · [TeX](manuscripts/uniform_growth_and_holder.tex), Theorem 1 and Proposition 5 | [PASS report](verification/reviews/MF-05-MF-07-review.md) |
| [MF-12](../../matrix-functions-and-stability/MF-12/README.md): Solved, affirmative | [PDF](manuscripts/arbitrary_growth_exponents.pdf) · [TeX](manuscripts/arbitrary_growth_exponents.tex), Theorem 1 and §§2–5 | [PASS report](verification/reviews/MF-12-review.md) |

**MF-05.** The joint spectral radius obeys a uniform exponent-$1/d$ Hölder estimate for every pair of nonempty compact real or complex matrix families in a common spectral-norm ball. The explicit constant is $d(2d+1)L^{1-1/d}$, improved to one when $d=1$. Restricting to a common bounded neighborhood gives the exact canonical local two-family statement, including reducible families and zero joint spectral radius. The sharpness example is a singleton weighted cyclic shift. No resolution of the separate MF-06 pointwise Lipschitz lower-bound problem is asserted.

**MF-07.** At joint spectral radius one, every switching product of length $k\ge1$ has norm at most $\Theta_d(Lk)^{d-1}$, with $\Theta_1=1$ and $\Theta_d=d(2ed^2/(d-1))^{d-1}$ for $d\ge2$. The constant depends only on dimension, with no dependence on the family or its cardinality. The result holds for bounded families as well as compact ones, over either field. The proof controls the change of coordinates and whole triangular products, without assuming an exact extremal norm or principal-submatrix monotonicity. The exponent is sharp; the constant is not claimed optimal.

**MF-12.** For every real exponent $\alpha\ge0$, two distinct real matrices yield joint spectral radius one and a maximal product norm between positive multiples of $k^\alpha$ for every integer $k\ge1$. The family is fixed after choosing the exponent. Six-dimensional pairs suffice for $0<\alpha<1$; order $6(\lfloor\alpha\rfloor+1)$ suffices for other noninteger exponents, and order $\alpha+1$ suffices for integer exponents. Every nonnegative rational exponent admits dyadic-rational entries. The result asserts comparability at every length, not convergence of the ratio to $k^\alpha$. Its constants depend on the chosen family, unlike the across-family constant in MF-07.

## Preserved submission and review hashes

All 17 original archive files are retained under [submitted/](submitted/), including the original TeX/PDF manuscripts, construction code, diagnostics, examples and preparation-stage audit material. The original bodies and their historical statements are preserved. The authored editions add the requested attribution and current review context. The [source manifest](verification/source-manifest.json) records the preserved files and source identities; the [document checks](verification/document-checks.json) record the authored-source and document validation.

The mathematical reviews bind the complete original UTF-8 sources after replacing CRLF by LF, without trimming:

| Original source | Complete normalized SHA256 |
| --- | --- |
| `MF-05_MF-07/uniform_growth_and_holder.tex` | `233df2a51c7666e447ac14bd51558704a3d3cb53db3e1738b79fe63d109406b5` |
| `MF-12/arbitrary_growth_exponents.tex` | `7a58a5086934410dc8c1172537a7b3031047094a7da577a5d3e24aaee21adf66` |

These are complete original-source hashes, not PDF hashes or hashes of selected proof excerpts. The reports distinguish universal proof checking from finite supporting computations. A substantive proof change would require a review update tied to the revised source.

## Historical HOLD and current public eligibility audit

The preparation environment could not inspect the live canonical pages and complete issue/PR records, so the archive placed submission on HOLD. That was an incomplete eligibility check, not a known mathematical objection. Its original status text and access limitations remain preserved in the submitted material and manuscript bodies.

The [live public eligibility record](verification/eligibility-live.json) supersedes those historical access limits for this submission. On 11 September 2026, it checked all three targets on 26 publicly visible branches across the upstream repository and reported forks: 78 canonical-page checks, all still Partially resolved. It examined public issue/PR bodies, discussion comments, reviews and changed-file records and found no matching existing resolution or pending review. These checks support clearing the archive's HOLD; they cannot exclude private or unpublished work, or arbitrary unlinked manuscripts elsewhere in a branch, and do not establish historical priority.

## Computational evidence and reproduction

The [separate computational review](verification/reviews/computational-review.md) checks the exact construction code, the relation between supplied evidence and the manuscripts, and fresh runs. The [fresh outputs and run manifests](verification/fresh-code/) retain the results and exact commands; the executed code is preserved under `submitted/construction/` and `submitted/verification/`. The construction tests, exact damping identity, real/complex damping and rescaling diagnostics, growth-word tests and finite exhaustive enumeration provide supporting evidence. They do not replace the analytical proofs for all dimensions, exponents, families, switching words or lengths.

In particular, the computational review reports six construction tests, 46,000 growth diagnostics, 10,000 damping tests, 5,000 finite-horizon tests and exhaustive enumeration through length 24, totaling 33,554,430 nonempty words. Counts describe finite verification coverage, not the range of validity of the theorems. The complete mathematical reviews supply the universal arguments and exact boundary-case analysis.

## Primary sources

1. J. Epperlein and F. Wirth, *The joint spectral radius is pointwise Hölder continuous*, Linear Algebra and its Applications 704 (2025), 92–122. [Primary preprint v2](https://arxiv.org/html/2311.18633v2), §2, Conjecture 3 (L1) and (L3); [DOI](https://doi.org/10.1016/j.laa.2024.09.016). These are the exact MF-05 and MF-07 targets.
2. J. Epperlein and F. Wirth, *Auerbach bases, projection constants, and the joint spectral radius of principal submatrices*. [Primary preprint](https://arxiv.org/html/2504.17505v1), 2025. This provides relevant normalization background and explains why a principal-submatrix shortcut would be invalid.
3. J. Varney and I. D. Morris, *On marginal growth rates of matrix products*, Linear Algebra and its Applications 709 (2025), 132–163. [Primary preprint](https://arxiv.org/html/2209.00449), §7, Question 2; Theorem 5, Corollary 6.1 and Proposition 3.1 provide the earlier growth-construction context. The new proof addresses the finite-family, every-length all-exponents target directly.

The original problem statements, permanent identifiers, canonical paths and historical ratings are retained. These three Solved classifications rest on the recorded independent agent proof reviews; no other canonical problem is claimed resolved by this record.
