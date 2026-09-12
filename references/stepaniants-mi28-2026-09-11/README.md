# MI-28 resolution by George Stepaniants — 11 September 2026

**Theorem 1:** for all positive definite $A,B\in\mathbb C^{n\times n}$, every $n\ge1$, $k\ge0$ and $0\le p\le2$,

$$
\det(A^k+|AB|^p)\ge\det(A^k+A^pB^p).
$$

The proof establishes a stronger log-majorization, includes every endpoint and resolves the entire canonical target. [Canonical entry](../../matrix-inequalities-and-norms/MI-28/README.md) · [Complete proof](../../matrix-inequalities-and-norms/MI-28/solution.md) · [PDF](../../matrix-inequalities-and-norms/MI-28/solution.pdf) · [Standalone TeX](../../matrix-inequalities-and-norms/MI-28/solution.tex).

## Authorship and verification

George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. His current affiliation was checked against his [official Caltech profile](https://www.cms.caltech.edu/people/george-stepaniants) and [personal academic page](https://georgestepaniants.com/) on 11 September 2026. Announced October appointments are not presented as current affiliations.

The work was developed with substantial ChatGPT/Codex assistance at the author's request. One agent developed two Furuta-based order implications; a second found the parameter interchange that closed the missing region. The first agent and the parent independently checked that step. A separate reviewer then audited the entire integrated proof and its applications of the primary sources. [Detailed independent PASS report](verification/reviews/MI-28-review.md).

The universal result rests on the analytic argument, not on the numerical searches used during discovery. This is independent automated-agent verification, not external human peer review or proof-assistant certification. No historical novelty or priority certification is asserted. The [original reviewed TeX](original-agent-manuscript.tex) and [matching Markdown](original-agent-manuscript.md) are retained as email-redacted copies, alongside the unchanged [parameter-interchange discovery note](parameter-interchange-discovery.md). At the author's request, the two manuscript headers had email metadata removed after review; every mathematical body is byte-identical, and the review addendum records both historical and current hashes. Earlier partial drafts are superseded by the complete proof.

## Imported results and exact scope

The previously established $k\ge2$ range is credited to Ghabries, Abbas, Mourad and Assi, *A proof of a conjectured determinantal inequality* (2020), [Lemma 2.5, manuscript p. 3](https://www.researchgate.net/publication/342908148_A_proof_of_a_conjectured_determinantal_inequality). The proof substitutes $X=A^{-1}$, $Y=B$, $K=k$, $s=2$, $t=p$ and retains the source restriction $0\le t\le s\le K$. No enlarged parameter range is attributed to that lemma.

The Löwner–Heinz and Furuta inputs were checked in [Tanahashi, *The Furuta inequality with negative powers* (1999), Propositions 1–2, p. 1683](https://www.researchgate.net/publication/255605812_The_Furuta_inequality_with_negative_powers). Every parameter condition is verified in the manuscript. The needed negative-power specialization is proved directly there using Löwner–Heinz and a singular-value identity. The independent review documents these source checks.

The new order argument covers $0<k\le2$, $0<p\le2$. Exterior powers give all partial products; equality of full determinants gives log-majorization. Continuity handles $k=0$, equality handles $p=0$, and convexity gives the exact determinant statement. Positive-exponent semidefinite cases follow by regularization; no convention for zeroth powers of singular matrices is asserted.

## Reproduction and documents

From the repository root, with Python 3, Pandoc and XeLaTeX available:

```bash
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
python3 tools/render_solutions.py MI-28
python3 tools/render_problems.py MI-28
```

Both exported TeX files compile independently with XeLaTeX. The preserved original agent TeX compiles with pdfLaTeX. [Document, identity and source-hash checks](verification/document-checks.json). Finite numerical tests are not represented as certificates for the universal inequality.

## Existing-submission check

The [dated public-network audit](verification/network-check.json) covers the parent, all recursively reported public forks, all 17 public branch heads then available, and upstream issues, pull requests and comments. Every canonical MI-28 page remained Partially resolved; no complete competing submission was found. Relevant named manuscript files were also checked. The audit cannot cover private, deleted or unpublished work.

## Submission

Prepared on the separate branch `sgstepaniants:codex/stepaniants-mi28-determinant` from the published base, preserving the permanent ID, canonical path and original mathematical target. [Resolution issue 84](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/84) follows the correction-or-resolution template. [Pull request 85](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/85) targets upstream `main` and explicitly asks the maintainer to review the complete proof, approve any required fork-workflow run and merge the resolution if accepted. Upstream acceptance is pending.

## Integration with updated upstream

After upstream advanced to `16369809e6e600144bd350ab70b7473b652f46f1`, the branch merged that published revision, retained its other resolutions, and regenerated the catalog from canonical metadata. All 203 permanent IDs and the original target match current upstream; all 17 safeguard tests pass. The authored proof sources and PDFs remain byte-for-byte identical to their reviewed versions without contact email.

## Integration with accepted main — 11 September 2026

The existing submission branch now retains accepted upstream changes from `87366c6` through a non-rewriting merge. The [dated integration record](verification/main-integration-2026-09-11-87366c6.md) documents unchanged reviewed proof files, preserved author attribution and mathematical targets, regenerated indexes, and passing ID/tests. Historical source hashes and reviews above are retained.
