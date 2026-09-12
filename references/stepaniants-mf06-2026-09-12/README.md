# MF-06 affirmative resolution - 12 September 2026 (UTC)

**Author:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA.

The [complete proof](../../matrix-functions-and-stability/MF-06/solution.md), Theorem (1), Lemmas 1-5 and Section 6, proves the original pointwise lower-Lipschitz perturbation bound for the joint spectral radius. It covers every nonempty compact complex reference family in every finite dimension, including reducible families whose normalized products are unbounded. The nearby family may be arbitrary. Constants depend on the fixed reference; the theorem is not a two-sided estimate uniform over two varying families.

[Proof PDF](../../matrix-functions-and-stability/MF-06/solution.pdf) · [Standalone TeX](../../matrix-functions-and-stability/MF-06/solution.tex) · [Retained canonical entry](../../matrix-functions-and-stability/MF-06/README.md).

## Mathematical source and independent audit

The complete [clarified candidate](reviewed-proof-clarified.md), 15,842 bytes, SHA-256 `11fce1e0012b8e514890fa6a116b8d91b91f56f5b7cd0ae20199006b4a18ca94`, passed the separate [independent Codex-agent mathematical audit](REVIEW.md). The reviewer did not author either the earlier partial argument or the full extension and reconstructed all five lemmas, the exterior-power reduction and transfer. The earlier partial audit was not used as a premise. The full report is 18,353 bytes, SHA-256 `6c15e3d3a20669ede243d7e56d1229f148e39a138e7c0d1628c5768cf6166d36`.

The [first full candidate](reviewed-proof.md) is retained unchanged. The sole [source clarification](source-clarification.diff) explicitly states the nonnegative parameters and nonempty scalar sequence in Lemma 2. The full reviewer verified that it changes no used hypothesis or deduction; no correction remains pending. The [comparison record](source-clarification.json) and [independent manifest](independent-manifest.json) bind the exact versions and supporting evidence.

The public Markdown's complete Sections 1-6 are byte-identical to the clarified source: 14,325 bytes, SHA-256 `95ffa57f417ac6e0bbc5e43da9f890d92384126f2cac41e2f282898ffb18bc4a`. The [source-preservation record](source-preservation.json) records the wrapper/attribution conversion and exact difference. All 182 ordered mathematical expressions are retained in the standalone TeX, with whitespace-only normalization. The [conversion checker](check_conversion.py) and [saved output](conversion-check-output.json) state their transcription scope.

The [frozen original target](canonical-target.md) is byte-identical to upstream main `1f22006bdaa4659fcaa0bb775a887685cd3cc566`, SHA-256 `fe32efa1f84a750039f65695f3cadbf615ead558826490e53329ca26704df741`. The canonical README retains its complete original definitions, statement and historical context from the context heading onward. Navigation inside the frozen copy is historical; use the live canonical link above.

Substantial AI assistance is disclosed. The full PASS is independent informal agent review, not external human peer review, formal verification, or a priority certification.

## Primary attribution and submission eligibility

The target is Epperlein and Wirth, *The joint spectral radius is pointwise Hölder continuous*, Section 2, Conjecture 3(P2), [arXiv:2311.18633v2](https://arxiv.org/html/2311.18633v2), published in LAA 704 (2025), 92-122, [DOI:10.1016/j.laa.2024.09.016](https://doi.org/10.1016/j.laa.2024.09.016). The standard positive-radius irreducible extremal-norm theorem retains Barabanov/Wirth attribution; a direct primary locator is Wirth's [Theorem 1.1, manuscript page 4](https://www.fim.uni-passau.de/fileadmin/dokumente/fakultaeten/fim/lehrstuhl/wirth/Publikationen/gsr.pdf).

Nonresonance and transition-sum estimates are prior theory of Chitour, Mason and Sigalotti, SCL 61 (2012), 747-757, [DOI:10.1016/j.sysconle.2012.04.005](https://doi.org/10.1016/j.sysconle.2012.04.005), especially discrete-time Theorem 20 on page 754 and Appendix Lemma 28 on page 757. The proof supplies its required paired-tensor formulation, without claiming those general mechanisms as new. Morris's [Lemma 3.2](https://arxiv.org/html/0909.2800v1) provides earlier second-exterior background under relative product boundedness. Exterior lifting itself retains prior attribution.

The separate [current public/source audit](public-audit/REPORT.md) checked six public repositories and all 49 returned heads at 05:04:43 UTC on 12 September 2026. Every canonical MF-06 page retained the same Partially resolved target. A [branch refresh at 05:19:51 UTC](public-audit/head-refresh.json) found 50 heads: the only addition was the separately submitted FR-12 branch, whose unchanged MF-06 canonical page and committed scope were checked. Upstream main and all prior heads remained unchanged. The audit inspected 153 selected text blobs, 177 issue/PR/comment records, and 32 PR review bodies. It found no already-public full resolution within its documented scope. The existing Colbrook MF-05/MF-07/MF-12 submission explicitly excludes MF-06 and retains its separate attribution. Precise primary locators, search queries and limits are in the [source record](public-audit/source-check.json) and [sanitized snapshot](public-audit/network-check-sanitized.json). Private, deleted, unpublished, unreturned, unidentifiably named and later work are outside this bounded check. Retrieved full bodies and third-party PDFs are not redistributed.

## Reproduction and document checks

From the repository root, run:

```sh
python3 references/stepaniants-mf06-2026-09-12/independent_exterior_check.py
python3 references/stepaniants-mf06-2026-09-12/check_conversion.py --original references/stepaniants-mf06-2026-09-12/reviewed-proof-clarified.md --markdown matrix-functions-and-stability/MF-06/solution.md --tex matrix-functions-and-stability/MF-06/solution.tex --review references/stepaniants-mf06-2026-09-12/REVIEW.md
python3 references/stepaniants-mf06-2026-09-12/build_solution.py --markdown matrix-functions-and-stability/MF-06/solution.md --tex matrix-functions-and-stability/MF-06/solution.tex --pdf
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/update_catalog.py --base-ref origin/main
python3 tools/render_problems.py MF-06
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
python3 -m unittest discover -s tests -p 'test_problem_statuses.py' -v
```

The source-conversion and independent algebra checkers use the Python standard library. The builder requires Pandoc and XeLaTeX, accepting `PANDOC` and `XELATEX` when needed. Both exported TeX documents are standalone. The final [verification record](verification.json) separates actual document/build/tests from mathematical review; the [manifest](manifest.json) binds the final publication files.

The independently written [exact algebra checker](independent_exterior_check.py) verifies 36 exterior-product identities, 279 diagonal allocation tensor blocks, 1,686 forced zero minors and 161 max/min factor reorderings on eight specified profiles through dimension six. Its [saved output](independent-exterior-check.json) states these finite scopes. These are supplementary transcription checks, not a numerical JSR estimate or a replacement for the proof's universal quantifiers.

The complete [independent publication-package review](packaging-review/REVIEW.md) records source/prose conversion, target correspondence, attribution, evidence bindings, live links and document text/privacy. Individual PDF pages are visually inspected by the recorded document reviewers. The final verification and manifest distinguish those checks from formal proof verification.

`Solved` is proposed under the repository's independent-informal-audit rule. Maintainer review and merge of the separate upstream pull request are required for inclusion in `main`. Every published ID and canonical path remains unchanged.
