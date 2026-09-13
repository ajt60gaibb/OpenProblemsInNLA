# RA-17 continuation submission

Author: **Sidney Holden**, Center for Computational Biology, Flatiron Institute, Simons Foundation.
Affiliation verified on 13 September 2026 using the [official Simons Foundation profile](https://www.simonsfoundation.org/people/sidney-holden/), which lists Flatiron Research Fellow, Biological Transport Networks, CCB, Flatiron Institute.

Original archive: `RA17_topological_relaxation_continuation.zip`.
SHA-256: `1fd960d0bb8c91b5d8d680b2d49aa50ce357ad11b159f44d42f8dc3363e33573`.
The supplied manuscript's blank author field was filled and its PDF rebuilt; mathematical content was retained. The submitted edition also discloses the informal audit and expands the Carlson bibliography title. `MANIFEST.sha256` is the original archive manifest, not a checksum claim for edited files. `prior/` contains unmodified provenance archives; it is not a submission of additional solutions. Historical logs describe the supplied bundle. Fresh review evidence is in [independent-review.md](independent-review.md).

## Duplicate and resolution checks

Checked upstream main and pushed fork branches and upstream PRs on 13 September 2026. [PR #197](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/197) submits earlier RA-17 partial results, not a full solution. This new PR is independently based on upstream main and adds the topological continuation without importing that PR's changes. No pushed full RA-17 solution was found. This submission adds the continuous odd-map and abstract bundle-frame criteria; neither implies constant linear measurements.

Status remains **Partially resolved** under CONTRIBUTING.md and RESOLVED.md. The exact counts at (6,1) and (10,1), and the general classification, remain unresolved in this submission. No Lean verification was performed, as requested. Independent review is informal AI-agent review, not external human peer review or formal verification.

## Reproduction

Run `python3 code/verify_relaxation.py` with SymPy installed, from this directory. Build `writeup/main.tex` twice with pdfLaTeX. The optional searches and archived interrupted calculations are not accepted certificates.

## Integration checks

Permanent IDs validated against `origin/main`; all 17 numbering safeguard tests passed. Catalog regeneration left counts and indexes unchanged. Repository math formatting and whitespace checks passed. The attributed manuscript compiled twice without LaTeX warnings; all 11 manuscript pages and both regenerated canonical problem pages were visually inspected. Removed RA-17 from the renderer's forced references-page-break list to avoid a nearly empty page after adding the continuation notice.
