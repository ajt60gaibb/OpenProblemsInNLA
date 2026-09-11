# Transfer and sampling submissions by Matthew J. Colbrook

**Author:** Matthew J. Colbrook. **Date:** 11 September 2026.  
**Affiliation:** Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom. **Email:** m.colbrook@damtp.cam.ac.uk. Affiliation checked against the [official Cambridge homepage](https://www.damtp.cam.ac.uk/user/mjc249/home.html).

This batch contains five supplied manuscripts and one supplied research note. Four complete catalog resolutions are independently verified: RA-07, RA-08, RA-09 and RE-05. RA-10 received a commuting partial result and a necessary lower bound in this batch. The Gamma manuscript refutes two auxiliary upper bounds; those examples alone left RA-12 and RA-13 Open. Subsequent complete proofs by George Stepaniants now resolve [RA-10](../../randomized-and-low-rank-approximation/RA-10/solution.md) and [RA-12](../../randomized-and-low-rank-approximation/RA-12/solution.md); their canonical entries retain this earlier evidence and attribution. RA-13 remains Open at this integration stage. Three separate Codex agents reviewed the complete arguments and precise scopes; six detailed reports record PASS within those scopes. The note was transcribed to TeX and independently checked, and the optional convex solver's failure branch was clarified and rechecked. The user's requested author byline appears on all six final manuscripts.

| Entry | Status supported by this historical submission | Primary manuscript locator | Independent review |
| --- | --- | --- | --- |
| [RA-07](../../randomized-and-low-rank-approximation/RA-07/README.md) | Solved | [Theorem 1.1](manuscripts/01_volume_sampling_convexity.pdf) | [PASS](verification/reviews/RA-07-review.md) |
| [RA-08](../../randomized-and-low-rank-approximation/RA-08/README.md) | Solved | [Theorem 3.1](manuscripts/03_concave_transfer_counterexamples.pdf) | [PASS](verification/reviews/RA-08-review.md) |
| [RA-09](../../randomized-and-low-rank-approximation/RA-09/README.md) | Solved | [Theorem 1.1, with the trace-deficit reduction in the entry](manuscripts/02_frobenius_function_transfer.pdf) | [PASS](verification/reviews/RA-09-review.md) |
| [RA-10](../../randomized-and-low-rank-approximation/RA-10/README.md) | Historical partial result; canonical target now Solved | [Theorem 1.1 and Section 3](manuscripts/06_commuting_schatten_transfer.pdf) | [PASS](verification/reviews/RA-10-review.md) |
| [RA-12](../../randomized-and-low-rank-approximation/RA-12/README.md) | Historical auxiliary result; canonical target now Solved | [Proposition 2.1 (with Proposition 3.1 for related evidence)](manuscripts/04_gamma_auxiliary_counterexamples.pdf) | [PASS](verification/reviews/gamma-auxiliary-review.md) |
| [RA-13](../../randomized-and-low-rank-approximation/RA-13/README.md) | Open | [Proposition 3.1 (with Proposition 2.1 for related evidence)](manuscripts/04_gamma_auxiliary_counterexamples.pdf) | [PASS](verification/reviews/gamma-auxiliary-review.md) |
| [RE-05](../../randomized-and-low-rank-approximation/RE-05/README.md) | Solved | [Theorem 2.1 and Proposition 5.1](manuscripts/05_linear_family_relative_sketch.pdf) | [PASS](verification/reviews/RE-05-review.md) |

## Exact scope

**RA-07.** The sequence $(j+1)e_{j+1}/e_j$ is decreasing and discretely convex for every positive spectrum, including both endpoints. The exact second-difference certificate proves the full canonical conjecture. 

**RA-08.** A rational positive definite $6\times6$ matrix and its exact rank-three Nyström approximation attain the optimal input spectral error but violate transformed optimality for $f(x)=\min(x,1)$. At $t=1/65536$, the output ratio is at least $1+334583/15769728$. Since the input excess is zero, this also excludes every finite factor $1+C\varepsilon$ for that scalar-concave class. 

**RA-09.** The ordered theorem transfers ordinary relative Frobenius residual error with no loss for the larger monotone subhomogeneous function class. Put $B=\widehat A_k$. Since $0\preceq B\preceq A$, $\|A-B\|_F^2=\|A\|_F^2-\|B\|_F^2-2\operatorname{tr}(B(A-B))\le\|A\|_F^2-\|B\|_F^2$. Thus the original stronger trace-deficit premise implies the proved residual premise, establishing the exact canonical conclusion. All specified eigenbasis choices and zero-tail cases are covered. 

**RA-10.** The sharp nuclear relative-excess factor is two when $A$, $B=\widehat A_k$ and the actual selected rank-$k$ projector have a simultaneous orthonormal eigenbasis. The finite-Schatten extension is also proved. Diagonal operator-monotone power examples show that any constant solving the full question must satisfy $C\ge2$. Existence of a finite universal constant for arbitrary noncommuting PSD pairs was open at that stage; the subsequent [complete proof with $C=11$](../../randomized-and-low-rank-approximation/RA-10/solution.md) settles the canonical target. Commutation of $A$ and $\widehat A$ alone does not cover every truncation inside a repeated eigenspace. The separate scalar-concave nuclear counterexamples use functions outside the required operator-monotone class.

**RA-12.** The submitted Gamma-density examples refute the upper-mode assertion in Hallman Conjecture 1 and the upper-inflection assertion in Conjecture 2, with legally distinct augmentation indices. These are counterexamples to auxiliary assertions. This auxiliary evidence neither proves nor refutes the complete relative Gaussian trace-tail probability chain and establishes no revised sharp tail threshold. RA-12 was Open at that stage; the subsequent [complete proof](../../randomized-and-low-rank-approximation/RA-12/solution.md) settles the original target.

**RA-13.** The centered augmented density has a genuine inflection point beyond the proposed auxiliary upper bound. Together with the mode example, this refutes the upper assertions of Hallman Conjectures 1 and 2. The complete absolute Gaussian trace-tail probability chain in this entry is neither proved nor refuted. Failure of an auxiliary sufficient condition does not refute the final tail comparisons; status remains Open.

**RE-05.** The nonadaptive two-sided algorithm achieves pure relative Frobenius error with $O(\sqrt{q(\log q+1/\varepsilon)}+\log q)$ queries at constant success. Fifteen independent copies with internal squared parameter $\varepsilon/9$ and the proved median selector give failure at most $e^{-4.8}<0.01$ and norm factor at most $1+\varepsilon$. This meets the exact canonical uniform query bound and arithmetic model. 

## Prior work and verification limits

The RE-05 manuscript acknowledges an earlier public announcement of the same spectral-splitting algorithm and pure relative-error result. The review accessed and compared the current [prior main source](https://raw.githubusercontent.com/andotheror/matvec-structured-matrix-approx/main/main.tex) and [supplement](https://raw.githubusercontent.com/andotheror/matvec-structured-matrix-approx/main/supplement.tex). Their displayed query profile has a squared logarithm; the submitted lower-tail argument is a valid proof route, but no priority or exhaustive novelty claim is made. Original draft statements that the full prior source was inaccessible are historical; the review records the later comparison. Zenodo deposit metadata and timestamp authenticity could not be verified, and the account name is not treated as independently verified personal identity.

Preparation and proof verification used Codex agents. This is independent agent review, not external human peer review, formal proof-assistant certification or an exhaustive novelty search. The mathematical reviews are separate from diagnostics; passing numerical samples is not proof of a universal assertion.

## Original identities and reviewed changes

[bundle-sha256.json](bundle-sha256.json) records the supplied zip and every contained file, computed on receipt. The original TeX, research note and supplied result JSON files are archived under [original](original). No checksum manifest was supplied. Each review records SHA-256 of its entire original UTF-8 source after CRLF-to-LF normalization, without trimming.

The [reviewed sources](reviewed-sources) preserve manuscripts 01--04 unchanged. Source 05 differs in one paragraph: the optional closed-convex extension reports failure before optimization if its Gram matrix does not dominate half the identity. On the accepted event, coercivity ensures existence and uniqueness; the failure probability is already covered. The independent reviewer checked this change and recorded both full hashes. The main linear-family result is unchanged. Source 06 is a faithful TeX transcription and explicit boundary/sharpness elaboration of the supplied commuting note; both original and final identities are recorded in its independent review.

The renderer inserts author, affiliation, date and the dated review notice, and embeds the complete reviewed mathematical body without editing it. Each exported TeX includes the common preamble and bibliography, so it compiles independently. The source hash and explicit body markers support comparison. The six Markdown manuscript pages are submission notes linking the full TeX/PDF proofs.

## Reproduction

The inspected [verification scripts](verification) use Python with NumPy, SciPy, SymPy and mpmath. All eight `verify_*.py` scripts were rerun successfully; their [rerun JSON results](results) are separate from the [supplied reports](original/results). They cover exact and symbolic identities, finite counterexample certificates, high-precision illustrations, and seeded matrix/sketch examples. Numerical examples of the convex optimizer use coefficient boxes; general convex optimization remains conditional on solving the stated optimization problem. Practical sketch sample overrides are explicitly outside the theorem's conservative guarantee, and the floating-point implementation is not a backward-stability certificate.

From the repository root:

```text
python -B references/colbrook-transfer-2026-09-11/verification/verify_volume_sampling.py
python -B references/colbrook-transfer-2026-09-11/verification/verify_frobenius_transfer.py
python -B references/colbrook-transfer-2026-09-11/verification/verify_relaxed_transfer.py
python -B references/colbrook-transfer-2026-09-11/verification/verify_counterexamples.py
python -B references/colbrook-transfer-2026-09-11/verification/verify_nystrom_counterexamples.py
python -B references/colbrook-transfer-2026-09-11/verification/verify_linear_family.py
python -B references/colbrook-transfer-2026-09-11/verification/verify_convex_family.py
python -B references/colbrook-transfer-2026-09-11/verification/verify_commuting_transfer.py
python -B tools/render_manuscripts.py references/colbrook-transfer-2026-09-11/manuscripts.json
python -B tools/update_catalog.py
python -B tools/render_problems.py RA-07 RA-08 RA-09 RA-10 RA-12 RA-13 RE-05
```

Pandoc and XeLaTeX are required for document regeneration; `PANDOC` and `XELATEX` may name their executables. Original canonical IDs, mathematical statements, references and dated prior audits are preserved. This is a new contribution branch from upstream main, separate from PR #6; the new pull request requests maintainer review and merge into main.

## Final document checks

All 13 final PDFs (six manuscripts and seven catalog entries, 41 pages) were rendered and visually inspected. All manuscript bylines and PDF author metadata were checked. The six exported mathematical bodies match their independently reviewed sources exactly; the seven original catalog statements, references and prior audits match the upstream base after removing the new notices and metadata changes. Relative links resolve, all eight diagnostics pass, and catalog regeneration is idempotent. [Document checks and final PDF hashes](verification/document-checks.json).
