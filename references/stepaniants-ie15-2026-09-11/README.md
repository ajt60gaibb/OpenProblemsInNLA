# IE-15 resolution by George Stepaniants — 11 September 2026

**Theorem 1:** the exact all-path rook-pivoting growth factors are $g_{\mathrm{RP}}(3)=3$ and $g_{\mathrm{RP}}(4)=14/3$. The proof includes global upper bounds, every intermediate active entry, all admissible ties and rational attaining examples. No requested case remains open.

[Canonical entry](../../linear-systems-and-elimination/IE-15/README.md) · [Complete proof](../../linear-systems-and-elimination/IE-15/solution.md) · [PDF](../../linear-systems-and-elimination/IE-15/solution.pdf) · [Standalone TeX](../../linear-systems-and-elimination/IE-15/solution.tex).

## Authorship and verification

George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. His current affiliation was checked against his [official Caltech profile](https://www.cms.caltech.edu/people/george-stepaniants) and [personal academic page](https://georgestepaniants.com/) on 11 September 2026. His announced Cambridge and NYU appointments start in October 2026 and are not presented as current affiliations.

The work was developed with substantial ChatGPT/Codex assistance at the author's request. A solving agent discovered the rational order-four example through constrained numerical optimization and developed the analytic upper bound. The parent agent checked the full argument, and a separate agent independently audited the exact target, every proof step, the scalar inequality and both witnesses. [Independent PASS report](verification/reviews/IE-15-review.md) · [Independent alternative scalar proof](verification/reviews/scalar-lemma-independent-proof.md). The [original reviewed agent manuscript](original-agent-draft.md) is retained as provenance.

This is independent automated-agent verification, not external human peer review or proof-assistant certification. Numerical experiments suggested the result; the upper bounds are proved analytically. The finite exact scripts certify the attaining examples, not the universal upper-bound argument. No historical novelty or priority certification is asserted.

## Reproduction

From the repository root:

```bash
python3 references/stepaniants-ie15-2026-09-11/verification/verify_witnesses.py
python3 references/stepaniants-ie15-2026-09-11/verification/independent_witnesses.py
python3 tools/render_solutions.py IE-15
python3 tools/render_problems.py IE-15
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
```

The witness scripts use Python's standard-library exact rational arithmetic. Rendering requires Pandoc and XeLaTeX. The exported TeX files compile independently. [Document and identity checks](verification/document-checks.json).

## Existing-submission check

The [dated network check](verification/network-check.json) covers the parent and every recursively reported public fork, all 16 public branch heads then available, and upstream issues/PRs and comments. IE-15 was Open on all checked branches. [Issue 71](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/71) and [PR 78](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/78) concern a related order-five lower bound and explicitly leave the requested orders three and four open. This submission concerns those two remaining exact constants.

The check is limited to publicly accessible material at its stated time; it cannot cover private, deleted or unpublished work. A separate IE-17 rediscovery from this session was withheld after the refreshed check found its existing resolution in PR 78. No duplicate IE-17 submission is included here.

## Submission

Prepared on the separate branch `sgstepaniants:codex/stepaniants-ie15-rook-growth` from the published base, with the permanent IE-15 ID, canonical path and original target unchanged. [Resolution issue 82](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/82) follows the correction-or-resolution template. [Pull request 83](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/83) targets upstream `main`, links the related order-five contribution, and explicitly asks the maintainer to review and merge the full resolution. Upstream acceptance is pending.

## Author metadata correction

At the author's request, the current submitted documents omit his email and retain his name, department and university. The preserved agent draft has the same contact-only redaction; its mathematical content is unchanged. The updated artifact fingerprints are recorded in the document checks.

## Upstream integration

The canonical entry incorporates upstream `main` at `16369809e6e600144bd350ab70b7473b652f46f1`. It retains Colbrook's complete attributed order-five note and verification links after the full resolution, with the note's earlier Open verdict identified as historical. The original target and all three mathematical proof files are unchanged. Only the canonical problem page was regenerated; both pages passed visual inspection. The [integration check](verification/reviews/IE-15-review.md#upstream-integration-check-11-september-2026) records this limited merge review.
