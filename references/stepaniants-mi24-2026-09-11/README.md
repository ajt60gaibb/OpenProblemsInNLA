# MI-24 resolution by George Stepaniants — 11 September 2026

**Theorem 1:** the full Schatten norm complement holds for every complex positive definite pair, every dimension and all $1\le p\le\infty$. No case in the canonical target remains open.

[Canonical entry](../../matrix-inequalities-and-norms/MI-24/README.md) · [Complete proof](../../matrix-inequalities-and-norms/MI-24/solution.md) · [PDF](../../matrix-inequalities-and-norms/MI-24/solution.pdf) · [Standalone TeX](../../matrix-inequalities-and-norms/MI-24/solution.tex).

## Authorship and verification

George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. His current department and university were verified against his [official Caltech profile](https://www.cms.caltech.edu/people/george-stepaniants) and [personal academic page](https://georgestepaniants.com/) on 11 September 2026. The author requests publication of his name, department and university without an email address. Announced Cambridge and NYU appointments begin in October 2026; the affiliation here is current as of the manuscript date.

The work was developed with substantial ChatGPT/Codex assistance at the author's request. The coordinating agent found the convexity deduction, and a separate agent independently checked the complete canonical argument and exact published theorem, including an alternative Schur-complement derivation of the positive matrix comparison. [Independent PASS report](verification/reviews/MI-24-review.md).

The proof uses Dinh, Dumitru and Franco's published Heron norm inequality, Theorem 4 on p. 2 of their author manuscript. The other matrix comparison is already in Ghabries, Abbas, Mourad and Assi, Corollary 4.1; the submitted proof derives it directly by polar decomposition. The added step uses $2Y=X+Z$ and $\|X\|_p\le\|Y\|_p$ to conclude $\|Y\|_p\le\|Z\|_p$ by the triangle inequality. Existing results retain their attribution. No numerical experiment is needed or represented as a universal proof.

Verification is independent automated-agent review, not external human peer review or proof-assistant certification. No historical novelty or priority certification is asserted. The exact reviewed-file hashes are retained, with a transparent addendum recording the author's contact-only metadata redaction.

## Reproduction

From the repository root:

```bash
python3 tools/render_solutions.py MI-24
python3 tools/render_problems.py MI-24
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
```

Rendering requires Pandoc and XeLaTeX. The exported TeX files compile independently. The solution template now makes contact information optional; no email is embedded in this submission. [Final document and identity checks](verification/document-checks.json).

## Existing-submission check

The [dated network check](verification/network-check.json) covers the parent repository and every recursively reported public fork, all 19 public branch heads available at 18:53 UTC on 11 September 2026, their canonical and ID-named text documents, and upstream issues/PRs and comments. MI-24 remained Partially resolved on every checked branch. No competing complete MI-24 submission was found. This is bounded evidence about publicly accessible material; private, deleted and unpublished work is excluded.

The primary problem source and the 2017 author-hosted manuscript were inspected directly. The full target is Conjecture 4.1 of arXiv:2105.13356v1; its Section 4 recalls the exact previously proved norm inequality and proves the other comparison. The source's trace/Frobenius cases do not limit the convexity deduction here.

## Submission

Prepared on a separate branch `sgstepaniants:codex/stepaniants-mi24-schatten` from the published base `ab754fabe3d48dc8d6eab6bcffce583e46d2b88f`, for a new pull request against `ajt60gaibb/OpenProblemsInNLA:main`. The permanent MI-24 ID, canonical path and original target are unchanged. [Resolution issue 90](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/90) follows the correction-or-resolution template. [Pull request 91](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/91) targets upstream `main` and explicitly requests maintainer review, fork-workflow approval if required, and merge upon acceptance. Upstream acceptance is pending.

## Integration with updated upstream

After upstream advanced to `16369809e6e600144bd350ab70b7473b652f46f1`, the branch merged that published revision, retained its other resolutions, and regenerated the catalog from canonical metadata. All 203 permanent IDs and the original target match current upstream; all 17 safeguard tests pass. The authored proof sources and PDFs remain byte-for-byte identical to their reviewed versions without contact email.
