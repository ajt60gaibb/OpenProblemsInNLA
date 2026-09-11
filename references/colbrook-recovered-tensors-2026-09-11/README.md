# Recovered tensor submissions — Matthew J. Colbrook, 11 September 2026

**Author:** Matthew J. Colbrook. **Affiliation:** Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom. **Email:** m.colbrook@damtp.cam.ac.uk. [Official affiliation](https://www.damtp.cam.ac.uk/user/mjc249/home.html), checked 11 September 2026.

The user supplied `tensor_solutions_recovered_complete.zip`. Its six manuscripts are recovered AI-generated candidate arguments, not claimed byte-for-byte restorations of unavailable earlier files. The original [recovery report](submitted/RECOVERY_REPORT.md) and [provenance](submitted/audit/provenance.json) are retained. Authorship is added at the submitter's request; the authored PDFs preserve the complete mathematical bodies from the independently reviewed sources. Independent agent verification is not external human peer review or formal certification. No priority or novelty claim is made.

## Duplicate exclusion

TR-06, TR-15 and TR-26 already have complete submitted solutions in [PR #97](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/97). Their recovered manuscripts, scripts, evidence and PDFs are excluded here; no duplicate resolution or replacement is proposed. Only TR-04, TR-13 and TR-20 are processed. Shared archive README/source notes are historical provenance and may mention excluded items; their relative links retain the original packaging and are not this submission's current index. The combined six-manuscript PDF and old embedded ZIPs are also omitted.

## Exact resolutions and review

### TR-04 — Strict pointwise TT approximation at prescribed ranks

A deterministic algorithm tests at most $n_1$ first-cut singular-subspace choices and TT-SVD completions. It returns a tensor within the prescribed ranks with squared error strictly less than $(d-1)E_*$ whenever $E_*>0$, and exactly reconstructs when $E_*=0$, in the canonical idealized arithmetic/SVD model. This settles the displayed pointwise target. It does not give a smaller uniform factor $c<d-1$ or a finite-precision bit-complexity guarantee; the fixed-format limiting example in Section 5 makes this distinction explicit.

[Canonical page](../../tensor-computations/TR-04/README.md) · [Authored PDF](manuscripts/TR-04.pdf) · [Authored TeX](manuscripts/TR-04.tex) · [Original complete TeX](submitted/manuscripts/TR-04/main.tex) · [Independent review](verification/reviews/TR-04-review.md). Locator: Theorem 3 and Sections 2–4.

### TR-13 — All generic rank equalities for odd-order Hankel tensors

For every odd $m\ge5$ and $n\ge2$, a nonempty Zariski-open set of complex Hankel tensors has ordinary rank, symmetric rank, ordinary border rank, symmetric border rank and Vandermonde rank all equal to $\lceil(m(n-1)+1)/2\rceil$. A compressed three-slice Koszul flattening gives the ordinary-border-rank lower bound, including arbitrary unstructured limiting sequences; a dominant moment map supplies the matching actual Vandermonde-rank upper bound. Exceptional Hankel tensors and the separate all-tensors question TR-14 are not settled.

[Canonical page](../../tensor-computations/TR-13/README.md) · [Authored PDF](manuscripts/TR-13.pdf) · [Authored TeX](manuscripts/TR-13.tex) · [Original complete TeX](submitted/manuscripts/TR-13/main.tex) · [Independent review](verification/reviews/TR-13-review.md). Locator: Theorem 1 and Sections 2–5.

### TR-20 — Both nonisotropic discriminant degrees for rank-one matrices

For every $n\ge2$, the reduced nonisotropic Rayleigh–Ritz discriminants in the original complex bilinear Segre model have degrees $24\binom{n+1}{3}$ for $2\times n$ matrices and $24n^2\binom n2$ for $3\times n$ matrices. The proof handles the logarithmic boundary and crossings, proves simple ramification and generic degree one onto the reduced irreducible image, and then extracts both formulas. Its general coefficient expression is additional to the two requested formulas.

[Canonical page](../../tensor-computations/TR-20/README.md) · [Authored PDF](manuscripts/TR-20.pdf) · [Authored TeX](manuscripts/TR-20.tex) · [Original complete TeX](submitted/manuscripts/TR-20/main.tex) · [Independent review](verification/reviews/TR-20-review.md). Locator: Theorem 1 and Sections 2–8.

## Provenance and reproducibility

The [archive manifest](verification/archive-manifest.json) records the ZIP hash, all archive paths/hashes, inclusion decisions and verification of all 64 supplied checksum entries before any diagnostic execution. The 27 retained files are byte-identical to their archive entries. Original evidence and PDFs remain under `submitted/`; fresh diagnostic results are separate in [verification/rerun](verification/rerun/).

All three full mathematical sources passed independent review against the original assumptions and primary references. Each review binds the entire UTF-8/LF source SHA256. The PDF builder additionally checks that everything from the original abstract through the end remains verbatim in the authored TeX. The preceding changes add only author/affiliation/date, disclosure and typesetting support.

Run `python verification/build_manuscripts.py` from this record to rebuild the three attributed PDFs with XeLaTeX (`XELATEX` may specify its executable). For fresh diagnostic reruns, copy the scripts under `submitted/code/` into a separate directory with a sibling `evidence/` directory, then run the selected scripts with NumPy and SymPy installed. Do not overwrite retained original evidence. TR-04 diagnostics use floating-point tolerances for numerical examples; the exact universal theorem is the independently checked analytic argument. TR-13 and TR-20 arithmetic diagnostics use exact symbolic/integer computation and supplement their general proofs.

[Final document and safeguard checks](verification/document-checks.json) record full-source identity, canonical target preservation, local links, exact diagnostic outcomes, permanent-ID validation, catalog idempotence and PDF inspection. All canonical README/TeX/PDF sets and the resolved catalog are updated together. GitHub publication follows the repository's issue-and-PR procedure against main.
