# RA-12 resolution by George Stepaniants - 11 September 2026

**Theorem 1:** both comparisons in the canonical relative Gaussian trace-tail chain hold for every nonzero real positive semidefinite matrix, every integer sample count $m\ge1$, every effective rank $\mu$, and every $\varepsilon\ge2/(m\mu)$. No case of RA-12 remains open. The stated threshold is valid; its optimality is not asserted.

[Canonical entry](../../randomized-and-low-rank-approximation/RA-12/README.md) · [Complete proof](../../randomized-and-low-rank-approximation/RA-12/solution.md) · [Proof PDF](../../randomized-and-low-rank-approximation/RA-12/solution.pdf) · [Standalone TeX](../../randomized-and-low-rank-approximation/RA-12/solution.tex).

## Authorship and verification

George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. His current department and university were checked against his [official Caltech profile](https://www.cms.caltech.edu/people/george-stepaniants) and [academic homepage](https://georgestepaniants.com/) on 11 September 2026. The submission publishes his name, department and university without contact email, as requested.

The work was developed with substantial ChatGPT/Codex assistance at the author's request. The research agent derived the mode bound and selected coefficient-transfer path; a separate independent Codex agent reconstructed and checked the entire proof against the exact canonical target, its external theorem, regularity, all endpoints and the Gamma limit. The coordinating agent also audited the argument. The [signed independent report](verification/RA-12-independent-review.md) records **PASS**. This is independent automated-agent verification, not external human peer review or formal proof-assistant certification. It is not a historical-priority certification.

The proof explicitly imports classical unimodality of heterogeneous Gamma convolutions from Roosta-Khorasani and Székely, *Schur properties of convolutions of gamma random variables*, Appendix A, Theorem 4; Lemma 5 supplies regularity. [Pinned primary text](https://arxiv.org/html/1601.04731v1). Hallman's Appendix A.1 supplies the coefficient-derivative method, which is derived again in the proof. The additional step selects the smaller changing coefficient to be a minimum positive scale. This restricted path supplies the required mode interval without invoking Hallman's disproved general upper-mode conjecture. Existing authors' results retain their attribution.

## Frozen source and mathematical integrity

The [frozen complete draft](full-proof-candidate.md) is preserved byte for byte, including its contemporaneous candidate label. That historical label describes its status before the independent review. Full source: 12,071 bytes; SHA-256 `247d615cab324975198b7b4f743deb44b45fd41a893224153603a2143be6b78f`.

The mathematical core begins with the literal `## The statement` and ends immediately before the literal `## Scope and relation to the auxiliary counterexamples`. It is 9,988 bytes, SHA-256 `29bf6811ba39b1f4e4507cb3b98daec6fc9d545809cf019c288a759e34154400`. The canonical `solution.md` core is byte-for-byte identical. Its packaging adds the complete affiliation and independent-review metadata outside this core. A local TeX spacing group around the reference list prevents an overfull line; it changes no bibliographic text or mathematics. The original review is preserved byte for byte at [its retained path](verification/RA-12-independent-review.md), with SHA-256 `a4d894666e2ccb896450701123cd9795a29b2e859022c8ce27984e98d9f22f72`; its historical relative link to the frozen draft still resolves.

The [original canonical page](original-canonical-README.md) records upstream main `16369809e6e600144bd350ab70b7473b652f46f1`. The problem statement is unchanged byte for byte in the updated page. The earlier Colbrook auxiliary results, author, manuscript links and independent-review links remain visible; the old statement that the full target remained open is explicitly presented as the historical scope of that earlier submission. No other problem ID or target is changed.

## Existing-submission check

The [retained network record](verification/network-check-latest.json) is copied unchanged from the coordinating agent's check at **2026-09-11 19:20:50 UTC**. It covers the parent repository and all recursively reported public forks: five repositories and all 21 available branch heads, canonical and ID-named text documents, and upstream issues, pull requests and issue comments. RA-12 was Open on every checked branch. Existing [PR 32](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/32) and [issue 31](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/31) concern auxiliary counterexamples and explicitly leave the full chain open. No competing complete solution was found in this bounded check. Private, deleted and unpublished work is outside its scope.

A separate [pre-publication confirmation](verification/network-before-push.json) at **2026-09-11 19:31:14 UTC** rechecked the same five repositories and 21 branch heads. RA-12 was still Open on every head, with only the same auxiliary issue, pull request and comment matches. The original 19:20:50 snapshot above is retained unchanged.

## Reproduction and submission

From the repository root, with Pandoc and XeLaTeX available:

```bash
python3 tools/render_solutions.py RA-12
python3 tools/render_problems.py RA-12
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
```

The generated TeX files compile independently. The shared solution template makes contact information optional. The final [document checks](verification/document-checks.json) record the preserved hashes, proof-core and original-target identities, author metadata, builds and visual inspection. The mathematical review uses no numerical experiment as a universal proof.

This package is published on `sgstepaniants:codex/stepaniants-ra12-gamma-tails`, an isolated branch from upstream main `16369809e6e600144bd350ab70b7473b652f46f1`. [Resolution issue 92](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/92) follows the correction-or-resolution template, and the new [pull request 93](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/93) targets `ajt60gaibb/OpenProblemsInNLA:main` and explicitly requests maintainer review and merge. Acceptance is pending. The reviewed artifact commit is `d8b18adf0f5355dfee2264a66d8287131446f972`. Catalog regeneration and all permanent-ID safeguard checks passed as recorded in the document checks.

## Integration with accepted main — 11 September 2026

The existing submission branch now retains accepted upstream changes from `87366c6` through a non-rewriting merge. The [dated integration record](verification/main-integration-2026-09-11-87366c6.md) documents unchanged reviewed proof files, preserved author attribution and mathematical targets, regenerated indexes, and passing ID/tests. Historical source hashes and reviews above are retained.
