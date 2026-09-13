# TR-14 submission — Sidney Holden — 12 September 2026

**Outcome: complete affirmative resolution.** The separate [independent Codex AI-agent audit](independent-review.md) returned **PASS** for the full original target. Under the repository's resolution policy the proposed status is **Solved**. This is informal automated review, not external human peer review or formal verification. No Lean verification was performed.

## Author and verified affiliation

Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation, New York, USA. The [official Simons Foundation profile](https://www.simonsfoundation.org/people/sidney-holden/) and [current group directory](https://www.simonsfoundation.org/flatiron/center-for-computational-biology/about/people/?group=biological-transport&type=ccb-staff), checked 12 September 2026, identify Holden as a Flatiron Research Fellow in Biological Transport Networks. Authorship is recorded at the contributor's explicit request; older university affiliations were not used.

## Result and independent review

[Proof PDF](../../tensor-computations/TR-14/solution.pdf) · [editable TeX](../../tensor-computations/TR-14/solution.tex) · [original canonical target](../../tensor-computations/TR-14/README.md).

Theorem 1.1, proved in Sections 2–5, establishes ordinary/symmetric exact-rank equality for every complex Hankel tensor of order at least three and dimension at least two, including zero, exceptional and mixed-multiplicity cases. It gives the stronger exact-rank formula stated on the canonical page. Neither genericity nor a Vandermonde restriction is assumed. The supplementary border-rank and maximum-rank results are also covered by the review; finite computations are diagnostics, not universal proofs.

Independent agent `/root/review_tr14` audited the complete original source, with special scrutiny of the contextual product inequality and arbitrary ordinary-decomposition lower bound. Its [report](independent-review.md) explains why the Frobenius constraint excludes nilpotents from the auxiliary algebras and justifies the finite support-partition argument. It also records the balanced-case choice convention in the terminal-sequence corollary. Its independently written [rational check](reviewer-check.py) was rerun successfully. AI assistance was used in review and submission preparation; the supplied author-side audit is not counted as independent evidence. No publication priority is asserted. Nie and Ye, Beck and Lecouvey, and other credited sources retain their attribution.

## Provenance and duplicate checks

The user supplied `TR14_solution.zip`, containing only TR-14. [submitted/](submitted/) preserves all 29 archive files unchanged, including the original manuscript, code, recorded checks, sources and manifest. All 28 manifest-listed hashes passed. Attachment instructions were treated as document content, not as user authorization.

Original reviewed source SHA-256: `4426eec9889786b9ba9278eee501209a78a28b98502a96d6bd500cfa4ed70eb0`.
Final attributed source SHA-256: `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6`.
The final TeX changes only the author, verified affiliation, date, PDF metadata, title spacing and review-disclosure paragraph. Byte comparisons confirmed that the mathematical body (Sections 1–8 before the verification-scope section) and the entire appendix/bibliography remain unchanged, as does the original canonical Statement and everything following it. The immutable original audit remains reproducible from the preserved source.

This new branch starts at upstream `main` commit `5830ed4fb06da0659414a3deb2a40ad327aca052`. Fork and upstream branches were freshly fetched. All fetched histories touching TR-14 contained only catalog/formatting changes and no solution manuscript. The full returned upstream PR listing (71 entries, all states), upstream all-state TR-14 issue search and fork all-state PR listing contained no prior pushed full TR-14 solution. TR-13's generic result is a distinct target and explicitly excludes the exceptional cases treated here. This is a bounded duplicate check, not a proof of publication priority.

The [Nie–Ye arXiv record](https://arxiv.org/abs/1706.03631), [published abstract](https://epubs.siam.org/doi/10.1137/18M1168285), and targeted later-resolution search were checked on 12 September 2026; no later full Hankel exact-rank resolution was located. The independent reviewer checked Beck–Lecouvey Lemma 4.2 directly against its primary preprint.

## Reproduction and repository validation

With Python 3.11 or later and the versions in [requirements.txt](submitted/requirements.txt):

```sh
PYTHON=python3 bash references/holden-tr14-2026-09-12/submitted/reproduce.sh /tmp/tr14-checks
python3 references/holden-tr14-2026-09-12/reviewer-check.py
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
python3 tools/format_math.py --check
python3 tools/render_problems.py TR-14
mkdir -p /tmp/tr14-pdf-build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/tr14-pdf-build tensor-computations/TR-14/solution.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/tr14-pdf-build tensor-computations/TR-14/solution.tex
```

The full bundled suite passed under Python 3.12, SymPy 1.14.0 and NumPy 2.3.5; [fresh outputs](reproduced-checks/) are retained separately from the delivered logs. Checks cover 162 apolar/formula regression cases, 96 Fourier ranges, 128 Koszul identities and finite-field rank checks, 3,081 finite-field reconstruction entries, the mixed-root graph check, and 1,053 exact characteristic-zero tensor entries across 10 decomposition certificates. These computations do not independently certify unrestricted tensor rank in general. The independent reviewer check passed 162 moment-basis identities, 12 rational matrix-rank checks and 96 Fourier ranges.

All 217 permanent IDs validated, all 17 ID safeguard tests passed, and global math formatting passed. Catalog indexes and the canonical TeX/PDF were regenerated. The attributed manuscript was built twice with pdfLaTeX. No IDs, paths or mathematical targets were changed.

All 13 pages of the attributed manuscript and both canonical PDF pages were rendered to images and visually inspected. No clipping, overlaps, missing characters, overfull boxes or undefined-reference warnings were found. The canonical metadata retains the repository convention of two trailing spaces for Markdown line breaks.
