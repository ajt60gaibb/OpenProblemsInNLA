# Matrix-function submissions by Matthew J. Colbrook

**Author:** Matthew J. Colbrook. **Date:** 11 September 2026.  
**Affiliation:** Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom. **Email:** m.colbrook@damtp.cam.ac.uk. Rechecked against the [official Cambridge homepage](https://www.damtp.cam.ac.uk/user/mjc249/home.html).

This batch contains six manuscripts. Three resolve full canonical targets (MF-03, MF-16 and SF-01), two establish partial results (MF-14 and MF-15), and one proves an auxiliary real-coefficient theorem without settling the general complex catalog target (MF-18). Three separate Codex agents independently checked all six full manuscripts, their hypotheses, proof steps, boundary cases and alignment with primary sources. This is independent agent proof review, not external human peer review or formal proof-assistant certification.

| Entry | Catalog status | Primary manuscript locator | Independent review |
| --- | --- | --- | --- |
| [MF-03](../../matrix-functions-and-stability/MF-03/README.md) | Solved | [Theorem 1](manuscripts/MF-03.pdf) | [PASS](verification/reviews/MF-03-review.md) |
| [MF-14](../../matrix-functions-and-stability/MF-14/README.md) | Partially resolved | [Theorem 1 and equations (1)-(2)](manuscripts/MF-14.pdf) | [PASS](verification/reviews/MF-14-review.md) |
| [MF-15](../../matrix-functions-and-stability/MF-15/README.md) | Partially resolved | [Theorem 1 and Corollary 4](manuscripts/MF-15.pdf) | [PASS](verification/reviews/MF-15-review.md) |
| [MF-16](../../matrix-functions-and-stability/MF-16/README.md) | Solved | [Theorem 1; Theorem 4 gives three certified solutions, and Theorem 3 gives a family threshold](manuscripts/MF-16.pdf) | [PASS](verification/reviews/MF-16-review.md) |
| [MF-18](../../matrix-functions-and-stability/MF-18/README.md) | Partially resolved; auxiliary result only | [Theorem 1 and Corollary 3; Section 8 exact defective example](manuscripts/MF-18.pdf) | [PASS](verification/reviews/MF-18-review.md) |
| [SF-01](../../matrix-functions-and-stability/SF-01/README.md) | Solved | [Theorem 1; Corollary 5 gives the Halley extension](manuscripts/SF-01.pdf) | [PASS](verification/reviews/SF-01-review.md) |

## Exact scopes

**MF-03.** For every integer $m\ge1$, the normalized diagonal Padé denominator for $\cosh\sqrt z$ is nonzero on $|z|\le3$ and $|1-r_m(z)|\le2$ there. The bound is strict for $m\ge2$ and sharp for $m=1$ at $z=3$. The analytic tail argument and exact finite certificates cover every order.

**MF-14.** A fixed seven-product scheme has a full-rank complex coefficient map, certified by a nonzero exact integer Jacobian minor. Its image contains a nonempty Zariski-open subset of $\mathbb C[x]_{\le42}$ and is Euclidean dense there. The upper bound excluding degree 43 and above is not proved. The maximal-degree equality remains open; neither exact representation of every polynomial nor real Euclidean dense coverage is asserted.

**MF-15.** The conventional critical exponent satisfies $\mathrm{CE}_n\ge2n-4$ for every $n\ge3$, already for rational entrywise nonnegative matrices with distinct positive eigenvalues. Combining this with the published upper bound gives $\mathrm{CE}_4=4$. The matching upper bound for every $n\ge5$, and hence the full family equality, remain unresolved. These are conventional matrix powers, not entrywise powers.

**MF-16.** The ordinary symmetric two-letter word $XBX^{12}BX=P$ has at least three distinct real symmetric positive definite solutions for explicit integer $B,P$. These are also Hermitian positive definite solutions, refuting the canonical universal uniqueness assertion in dimension two. An exact negative Jacobian determinant and two independent interval implementations certify the counterexample.

**MF-18.** For real $A,Q$ with $Q=Q^\top$, scalar regularization $i\eta I$, and a finite invertible stabilizing limit, the manuscript proves that the imaginary-part rank is half the number of odd unit-circle Jordan blocks. It also establishes semisimple regularity and an exact defective example. This does not settle the canonical general complex $C,D,R,P$ problem. Its simple-eigenvalue real subcase was already known; the defective extension is an auxiliary result outside the canonical simple-eigenvalue hypothesis. The existing partial status and general complex target are retained.

**SF-01.** Every exact Newton square-root iterate initialized at $X_0=A$ remains a real nonsingular H-matrix with positive diagonal. The theorem includes arbitrary positive scalar scaling and nonnegative affine initializations, with one diagonal-dominance weight for all iterates; it also proves the corresponding Halley preservation result.

## Source provenance and attribution

The [archive manifest](bundle-sha256.json) records the supplied zip and every contained file by SHA-256. Original standalone TeX manuscripts and supplied JSON certificates are preserved under [original](original); [reviewed sources](reviewed-sources) are the inputs to the authored exports. The author, affiliation, date and a review/scope notice are added without changing the reviewed body after the title command. Each export retains its complete standalone preamble and bibliography. Original supplied PDFs and the supplied preview image are identified in the archive manifest; the final PDFs are regenerated from reviewed TeX.

MF-14's reviewed text corrects its description of the supplied verifier: the archive includes the exact integer implementation but omits the earlier discovery program. The independent report records the original and revised source hashes and the wording changes. No new discovery implementation is invented. The degree-42 scheme itself is attributed to Jarlebring and Lorentzon. The MF-15 order-four equality uses the published upper bound. MF-16 credits the Armstrong--Hillar degree theorem, while its interval proof also provides an independent existence certificate. SF-01 identifies prior Newton, Halley and partial-fraction work. MF-18's simple-eigenvalue real subcase was already known and is not presented as a resolution of the general complex question. No exhaustive novelty search or priority certification is claimed.

## Reproduction

All seven supplied certificate programs in [code](code) were inspected and successfully rerun using Python's standard library. Fresh outputs in [results](results) agree with all six supplied output reports that could be independently regenerated. The supplied degree-42 parameter certificate is retained as the input to the exact integer audit. A new independent rational-interval report for the word equation was generated; it was not present in the input archive. Original results remain separately preserved.

From the repository root, run all seven supplied checks with:

```text
python -X utf8 -B references/colbrook-matrix-functions-2026-09-11/code/run_certificates.py
```

An additional reviewer-created [symbolic Jacobian audit](verification/reviewer_mf16_algebra.py) has a [recorded result](verification/reviewer_mf16_algebra.json). This optional check requires SymPy 1.14 and imports none of the submitted code; the seven supplied programs require only the standard library.

Alternatively, run the commands in each manuscript from this submission folder, where the original `code/` and `results/` paths are preserved. The finite certificates prove the specific exact identities and interval inclusions they check. The all-order and all-dimension theorems rest on the independent analytic reviews. In particular, the MF-18 finite certificate does not prove general convergence or the odd-block formula, and MF-14's determinant does not establish maximality.

Regenerate the authored manuscripts, indexes and canonical documents using:

```text
python -X utf8 -B tools/render_reviewed_tex.py references/colbrook-matrix-functions-2026-09-11/manuscripts.json
python -X utf8 -B tools/update_catalog.py
python -X utf8 -B tools/render_problems.py MF-03 MF-14 MF-15 MF-16 MF-18 SF-01
```

Pandoc and XeLaTeX are required for document generation; `PANDOC` and `XELATEX` can specify their executables. The authored renderer requires a complete source hash matching its independent PASS review. The original canonical IDs, mathematical statements, references and audit history are preserved. This new branch is based directly on upstream main, independent of PR #6, PR #32 and PR #40; maintainer review and merge into main are requested.

## Final document checks

The [machine-readable checks](verification/document-checks.json) record final PDF hashes and page counts, complete reviewed-body identity, original canonical content preservation, source provenance, author metadata, local links, catalog idempotence and the seven successful certificate runs. All 40 pages of the twelve final PDFs were visually inspected, and compilation produced no layout or reference warnings. The branch contains 202 catalog entries: 113 Open, 84 Partially resolved, one Solution claimed and four Solved, giving an open count of 197.
