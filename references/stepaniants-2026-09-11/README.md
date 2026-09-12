# AA-01, MD-03 and MD-04: reviewed submissions by George Stepaniants

**Submission author:** George Stepaniants.  
**Current affiliation:** Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA.  
**Submission and independent review date:** 11 September 2026.

The byline is included at the author's explicit request. The current affiliation was checked against the [official Caltech profile](https://www.cms.caltech.edu/people/george-stepaniants) and [personal academic website](https://georgestepaniants.com/) on 11 September 2026. The website lists an Assistant Professorship in Cambridge's Department of Applied Mathematics and Theoretical Physics and a visiting-faculty appointment at NYU Courant beginning in October 2026; these future appointments are not presented as current affiliations.

## Results and attribution

| ID | Exact result | Primary manuscript and locator | Independent review |
| --- | --- | --- | --- |
| [AA-01](../../arithmetic-and-complexity/AA-01/README.md) | An always-halting decision procedure for the displayed constant-free finite-tree model; an evaluator is constructed on positive instances. | George Stepaniants, [complete proof](../../arithmetic-and-complexity/AA-01/solution.tex) ([PDF](../../arithmetic-and-complexity/AA-01/solution.pdf)), Theorem 2.1 and Corollary 7.1. | [PASS](verification/reviews/AA-01-review.md) |
| [MD-03](../../matrix-discrepancy-and-optimization/MD-03/README.md) | Universal Komlós constant $3\sqrt{2\pi}$ for all positive dimensions. | Guo, Fang and Lu, [arXiv:2609.11189v1](https://arxiv.org/abs/2609.11189v1), Theorem 1.1, p. 1; Stepaniants's [application note](manuscripts/md03_md04_proofs.tex) ([PDF](manuscripts/md03_md04_proofs.pdf)), Theorem 1. | [PASS](verification/reviews/MD-03-MD-04-review.md) |
| [MD-04](../../matrix-discrepancy-and-optimization/MD-04/README.md) | Beck–Fiala bound $3\sqrt{2\pi t}$ for every permitted sparsity. | Guo, Fang and Lu, [arXiv:2609.11189v1](https://arxiv.org/abs/2609.11189v1), Corollary 1.2, p. 2; Stepaniants's [application note](manuscripts/md03_md04_proofs.tex) ([PDF](manuscripts/md03_md04_proofs.pdf)), Theorem 2. | [PASS](verification/reviews/MD-03-MD-04-review.md) |

George Stepaniants is the author of the submitted AA-01 argument and the explanatory MD-03/MD-04 application note. The discrepancy theorems and their priority are credited to **Shengtao Guo, Ethan X. Fang and Junwei Lu**. The note makes no new discrepancy-theorem claim. Its source-preprint qualification is retained.

## Verification and provenance

Two separate Codex review agents covered the three exact targets. The AA-01 reviewer checked the complete coupling, polynomial-interpolation, evaluator-construction and quantifier-elimination argument, including independent rounding, stored reuse, error-dependent comparisons, zeros and boundary cases. The discrepancy reviewer checked both applications and the substantive proof of the cited preprint, including its published eigenvalue-convexity input; its report is not limited to matching theorem statements. Both reviewers returned PASS without a mandatory mathematical correction.

The manuscripts were supplied in a ChatGPT conversation, and this provenance is retained. The discrepancy source discloses use of the Odin AI research agent. The verification recorded here is **independent automated-agent review**, not external human peer review, community acceptance, or a formal proof certificate. No exhaustive novelty claim is made for AA-01. The manuscript's formal-verification reference concerns the external real-quantifier-elimination algorithm, not the new AA-01 proof.

Under the repository's [status definition](../../RESOLVED.md), the reviewed exact targets are proposed as **Solved**. The original IDs, paths, mathematical statements, references and earlier status evidence are retained; the old difficulty and importance assessments are historical.

## Eligibility and duplicate-submission check

The submission starts from parent `ajt60gaibb/OpenProblemsInNLA` commit `ab754fabe3d48dc8d6eab6bcffce583e46d2b88f`. AA-01 and MD-03 were Open, and MD-04 was Partially resolved with its unrestricted target still open. None was Solved or Solution claimed in the published base.

The public GitHub network was checked twice on 11 September 2026 before submission: the parent plus all four public forks (`sgstepaniants`, `k1monfared`, `MColbrook`, and `bonans`), comprising 12 branch tips and nine distinct commits. Full branch snapshots were searched for the three IDs and mathematical titles. All three canonical pages were identical across every branch, and no additional resolution manuscript was found. The refresh found no new branch commits and no matching title or body among the parent's 62 issues and pull requests. The seven PRs, 16 issue comments and two review comments were also checked in the initial audit; none mentioned these targets. This check covers publicly accessible current branches, not private or deleted branches.

The [machine-readable network inventory](verification/network-check.json) records every checked branch and its commit. The new submission branch is intentionally separate from earlier contributors' resolution PRs. Submission does not imply acceptance into upstream main.

## Public submission

The completed submission was pushed to `sgstepaniants:codex/stepaniants-aa01-md03-md04-resolutions` in [commit 7a732d7](https://github.com/sgstepaniants/OpenProblemsInNLA/commit/7a732d7532dbc7802266a6972a0c53f4da18453a). The correction-or-resolution reports are [AA-01, issue #65](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/65), [MD-03, issue #66](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/66), and [MD-04, issue #67](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/67).

[Pull request #68](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/68) targets `ajt60gaibb/OpenProblemsInNLA:main`, links all three issue reports for closure on merge, and explicitly asks the maintainer to review and merge the contribution. Upstream review and acceptance are pending.

## Rebuilding

Canonical pages are regenerated with the repository's existing Pandoc/XeLaTeX renderer:

```bash
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
python3 tools/render_problems.py AA-01 MD-03 MD-04
```

The two submitted manuscript sources are standalone and use pdfLaTeX. Compile each twice in a temporary output directory, then copy only the resulting PDF beside its source:

```bash
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp arithmetic-and-complexity/AA-01/solution.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp arithmetic-and-complexity/AA-01/solution.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp references/stepaniants-2026-09-11/manuscripts/md03_md04_proofs.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp references/stepaniants-2026-09-11/manuscripts/md03_md04_proofs.tex
```

The [document-check record](verification/document-checks.json) records the final build, source hashes and preservation checks.

## Integration with updated upstream

After upstream advanced to `16369809e6e600144bd350ab70b7473b652f46f1`, the branch merged that published revision, retained its other resolutions, and regenerated the catalog from canonical metadata. All 203 permanent IDs and the original targets match current upstream; all 17 safeguard tests pass. The authored proof sources and PDFs remain byte-for-byte identical to their reviewed versions without contact email.

## Integration with accepted main — 11 September 2026

The existing submission branch now retains accepted upstream changes from `87366c6` through a non-rewriting merge. The [dated integration record](verification/main-integration-2026-09-11-87366c6.md) documents unchanged reviewed proof files, preserved author attribution and mathematical targets, regenerated indexes, and passing ID/tests. Historical source hashes and reviews above are retained.
