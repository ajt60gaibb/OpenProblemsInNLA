# MI-16 final publication audit

Date: 2026-09-13 UTC. Reviewer: separately delegated Codex AI agent `/root/independent_mi16_review`. Scope: bounded review of publication changes following the full independent mathematical audit. No Lean verification performed.

**Verdict: PASS.** The published form accurately presents the independently audited all-spectrum result as an exact finite algebraic prescription, retains the original mathematical target, credits Sidney Holden as requested, discloses AI assistance and the actual review level, and preserves the special-family prior-result attribution. No blocking publication defect was found in the inspected material.

## Files inspected

- `matrix-inequalities-and-norms/MI-16/README.md`
- `matrix-inequalities-and-norms/MI-16/solution.tex`
- Authored solution PDF title-page rendering `/tmp/mi16-pdf-build/final-01.png`
- `references/holden-mi16-2026-09-12/README.md`
- Archived `dossier/paper/mi16_dossier.tex`
- Published `independent-review.md` and `reviewer-check.py`
- New MI-16 entry in `RESOLVED.md`

## Preservation and scope checks

1. Confirmed the active branch is `codex/holden-mi16-algebraic-resolution`.
2. Compared the entire original Problem statement section, through the exact-value completion criterion, against `upstream/main`: **byte-identical**. Its every-order, every-nonnegative-real-spectrum quantifiers are unchanged.
3. Compared authored `solution.tex` from the first section marker through end-of-file against the archived dossier source: **byte-identical**. The proof reviewed earlier has not been changed during attribution or layout preparation.
4. Authored solution source SHA-256 at review: `57fa815259b0fcfe658e3ed8502d4494cf0c2e8a993c60d647e976468c5232d1`.
5. Confirmed the published independent review is byte-identical to the reviewer's report and the published independent checker retains SHA-256 `eff130b81cb0fb01750d617c1012131309fc3ce5d188905d34777980c436eb25`.
6. The canonical notice and resolution archive clearly distinguish the all-spectrum algebraic result from the separate one-exceptional-eigenvalue structural formula. They disclose exact ordered-field interpretation, rational-only reference code, computational limitations, and absence of a general optimizer classification or compact structural formula.
7. `Solved` is justified by the literal retained target and independent proof audit under the repository's explicit AI-agent-review policy. The notice exposes the historical structural-formula interpretation to maintainers instead of claiming historical community acceptance.

## Attribution and presentation

Sidney Holden appears as author on the title page, PDF-author source metadata, canonical notice, submission README, and resolution archive. The stated affiliation is consistently Center for Computational Biology, Flatiron Institute, Simons Foundation. The submission README supplies official institutional profile and directory links with a verification date. This publication review checked attribution consistency and the presence of supporting links; the integrating agent performed current-affiliation source verification.

The title page states ChatGPT assistance and distinguishes informal AI-agent audit from external human review or formal verification. The original rank-one expansion and equal-support reduction remain credited to the prior partial findings, with PR #186 linked in publication notices. Duplicate checking and the historical relationship with pending PR #194 are clearly described as a bounded repository check, not a novelty certificate.

The title-page image is readable, properly spaced, and displays the full author, affiliation, scope, assistance and prior-findings notices without clipping or overlap. Full-PDF page inspection and final publication/provenance checks are assigned to the integrating agent. At inspection time the reference README linked `publication-checks.md`, which was still being prepared; that file must be present before committing the final publication.
