# RA-10 resolution by George Stepaniants - 11 September 2026

**Theorem 1:** the full canonical constant-loss nuclear-error implication holds with the universal constant $C=11$. This covers arbitrary real positive semidefinite pairs, all dimensions and allowed ranks, every selected ordered eigenbasis, every nonnegative continuous operator-monotone function and every nonnegative relative tolerance. No case of the canonical target remains open; sharpness of 11 and other norms are not asserted.

[Canonical entry](../../randomized-and-low-rank-approximation/RA-10/README.md) · [Complete proof](../../randomized-and-low-rank-approximation/RA-10/solution.md) · [Proof PDF](../../randomized-and-low-rank-approximation/RA-10/solution.pdf) · [Standalone TeX](../../randomized-and-low-rank-approximation/RA-10/solution.tex).

## Authorship and mathematical review

George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. The department and university were checked against his [official Caltech profile](https://www.cms.caltech.edu/people/george-stepaniants) and [academic homepage](https://georgestepaniants.com/) on 11 September 2026. His name and affiliation are published with his authorization; no contact email is included.

The work was developed with substantial ChatGPT/Codex assistance at the author's request. The coordinating agent derived the new compression estimate and the full constant-11 proof. A separate Codex agent independently reconstructed the compression algebra, constants and integral reduction and audited the entire frozen proof against the exact target. Its [complete independent report](verification/RA-10-independent-review.md) records **PASS**, including arbitrary truncation ties, singular compressions, selected zero eigenvalues, $f(0)>0$ and zero optimal tail. A [supplementary independent audit](verification/eigenvalue-and-notation-audit.md) proves the eigenvalue comparison directly from min-max and checks the selected functional calculus.

This is independent automated-agent review, not external human peer review, formal proof-assistant verification or certification of historical priority. The final mathematical argument uses no numerical experiment. The main external analytic input is Chansangiam, [arXiv:1304.7936v1](https://arxiv.org/pdf/1304.7936v1), Proposition 1.1, page 2: the positive integral representation of operator-monotone functions. The proof gives the measure conversion explicitly.

## Frozen sources and faithful conversion

The [frozen original draft](full-proof-candidate.md) is retained byte for byte: **11,521 bytes**, SHA-256 `eaf566e469e1c3a5a21473852c29247d86e7960f87178d0245ea7f89379e8e35`. Its original candidate/pending-review label is preserved as historical provenance; the completed review follows that version.

The complete independent report is also retained byte for byte: **9,180 bytes**, SHA-256 `c1d6664ea1099671fa2603d99170b11a96512dbdafbfbdf76a22b2cc500bb1ad`. The supplementary report has SHA-256 `e987537fc7a18a36dc864bfed6fd69d6eebb8a70041a44871ff7c693bc55dad0`.

The published Markdown converts the frozen draft's ASCII notation to LaTeX and adds author and review metadata. Its only explanatory mathematical addition is the independently supplied min-max proof of the already-used eigenvalue comparison (16). It preserves the theorem, compression estimate, all 22 equation labels, constants and boundary cases. The coordinating agent checked the complete conversion against both independently reviewed sources. This packaging check is distinguished from the separate agent's mathematical review; the latter binds the frozen original and supplement. Final file identities and conversion details are recorded in [document checks](verification/document-checks.json).

The [original canonical page](original-canonical-README.md) is copied from upstream main `16369809e6e600144bd350ab70b7473b652f46f1`. Its complete mathematical target, beginning with `Does a universal constant` and ending immediately before `## References`, remains byte-for-byte unchanged: **1,253 bytes**, SHA-256 `80ca04cbb4aad1690c960c900eb22c01765ca7069a56f4d5c1670750b250b392`.

Matthew J. Colbrook's earlier commuting theorem, lower bound $C>=2$, author, manuscript links and independent review remain visible. Its former remaining-question sentence is explicitly historical. The full resolution changes no published ID or canonical path, and the original ratings remain labeled as historical.

## Existing-submission check

The [public-network snapshot](verification/network-check.json) records a check at **2026-09-11 20:30:17 UTC** of the network source and every recursively reported public fork: **five repositories and all 24 public branch heads**. Every checked canonical RA-10 page was **Partially resolved**. The check fetched canonical and relevant named text documents and root indexes, and examined matching issues, pull-request bodies, issue comments and inline review comments in all five repositories. Unrelated text from root indexes is omitted from the published snapshot; its path/blob identities and the hash of the complete local fetch are retained.

The two distinct canonical pages, generated TeX, separate review, scoped index passages and the three matching discussion records contain no competing complete solution. [Issue 30](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/30) and [PR 32](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/32) expressly leave arbitrary noncommuting nuclear transfer open. The original [Persson-Meyer-Musco source](https://arxiv.org/html/2311.14023v2), Section 1.2 and the closing paragraph of Section 5, leaves a larger fixed constant possible; the cited 2026 Krylov work addresses particular algorithms. This bounded search found no competing full resolution. Private, deleted, unpublished or unidentifiably named work is outside its scope.

A [final pre-publication confirmation](verification/network-before-push.json) at **2026-09-11 20:45:23 UTC** rechecked the same five repositories and 24 branch heads. All canonical pages remained partial, and the same three discussion matches contained no complete solution.

The portable [read-only network checker](verification/network_check.py) can be rerun with an authenticated GitHub CLI:

```bash
python3 references/stepaniants-ra10-2026-09-11/verification/network_check.py --output /tmp/ra10-network-check.json
```

## Reproduction and submission

From the repository root, with Pandoc and XeLaTeX available:

```bash
python3 tools/render_solutions.py RA-10
python3 tools/render_problems.py RA-10
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
```

The shared solution template makes its email field optional. Both exported TeX files compile independently. The [document checks](verification/document-checks.json) record actual builds, every-page visual inspection, permanent-ID validation and final artifact hashes.

The submission branch is `sgstepaniants:codex/stepaniants-ra10-nuclear-transfer`, based on the upstream main commit above. The correction-or-resolution issue and new pull request target `ajt60gaibb/OpenProblemsInNLA:main`. They are listed in the [author's RA-10 submission discussions](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues?q=RA-10+author%3Asgstepaniants); the pull request links its resolution issue and explicitly requests maintainer review and merge. Maintainer acceptance and merge are separate from the documented mathematical review.
