# PF-01 second-round structural results — Sidney Holden

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation.

Affiliation verified on 13 September 2026 against the [official Simons Foundation profile](https://www.simonsfoundation.org/people/sidney-holden/) and [current group directory](https://www.simonsfoundation.org/flatiron/center-for-computational-biology/about/people/?group=biological-transport&type=ccb-staff), which list Holden as a Flatiron Research Fellow in Biological Transport Networks. The byline is supplied at the author's request; it does not imply institutional endorsement.

**Independent Codex AI-agent review: PASS for new partial structural results. PF-01 remains Partially resolved.** [Authored manuscript](paper/pf01_structural_obstructions.pdf) · [Editable TeX](paper/pf01_structural_obstructions.tex) · [Independent report](verification/independent-review.md).

The reviewed contribution comprises Sections 2–10: affine reduction at order nine, rank-one-factor counting (65 of 70 at order eight; 64 of 126 at order nine), the span-five projection-family theorem, mixed-rank and 252 covering constraints, and the exact 90-dimensional quartic derivative space with its nine indispensable extra directions. The exact PSD rank for n >= 7 remains undetermined. No status promotion to Solved is justified under CONTRIBUTING.md and RESOLVED.md.

The earlier general bounds in Section 1 and the nested prior archive are background research claims outside this independent review's scope. They are not newly endorsed by the catalog. Colbrook retains credit for the previously reviewed finite cases and bounds. The submission's own statements that no independent review occurred describe its original state; the separately dated report records the review performed for this PR.

## Provenance and duplicate check

The complete original package is retained unchanged under [submitted/](submitted/README.md), including its manifest and prior archive. The top-level archive SHA-256 is recorded in [input-sha256.txt](verification/input-sha256.txt). The authored export changes only title metadata, author/date, and title spacing; the mathematical body is unchanged. Original manuscripts and nested archives retain their historical bylines and attribution.

Upstream main at 5830ed4 and all fetched fork branches were checked on 13 September 2026, together with all-state upstream PR search for PF-01. Existing [PR #40](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/40) records partial results; no previously pushed full PF-01 solution was identified. This new submission therefore passes the requested duplicate exclusion. Permanent ID, path, original target, ratings and existing attribution are retained.

## Reproduction and review limits

From `submitted/`, install `requirements.txt`, then run `python code/verify_round2.py` and `python code/verify_prior.py`. Both programs were rerun successfully on 13 September 2026; logs are [round2-rerun.log](verification/round2-rerun.log) and [prior-rerun.log](verification/prior-rerun.log). These checks do not audit the prior manuscript's general proofs. The [separate reviewer-written checker](verification/independent-check.py) uses Python/NumPy and a second prime, 1000033; run it from any directory. Its [output](verification/independent-check.json) records the exact rank and combinatorial checks.

Build the authored TeX twice with pdfLaTeX. The canonical page is built with `python3 tools/render_problems.py PF-01`. PDF pages were rendered and visually inspected. AI assistance was used in submission preparation and the independent informal mathematical audit. No Lean verification, formal certification, external human peer review, or novelty certification is asserted.
