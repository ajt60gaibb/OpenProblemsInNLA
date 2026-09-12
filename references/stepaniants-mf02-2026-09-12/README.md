# MF-02: uniform constant-factor cubic-composition overhead

Author of this expository proof note: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA.

Recorded 12 September 2026. [Canonical retained problem](../../matrix-functions-and-stability/MF-02/README.md) · [Complete proof](../../matrix-functions-and-stability/MF-02/solution.md) · [Standalone TeX](../../matrix-functions-and-stability/MF-02/solution.tex) · [Proof PDF](../../matrix-functions-and-stability/MF-02/solution.pdf).

## Exact resolution and limits

The literal canonical request for asymptotic dependence is resolved: $T_{\min}(m,\delta)=\Theta(m+1)$ uniformly over every $0<\delta<1$, including gaps depending on the budget. The theorem gives $\lfloor m/2\rfloor\le T_{\min}\le m$ for $m\ge2$ and $T_{\min}(0,\delta)=T_{\min}(1,\delta)=1$. All original definitions, targets, references and dated history remain unchanged. Historical ratings and all 217 permanent ID/path mappings are retained.

The exact minimum, an optimal leading constant, and the stronger source comparison of approximation errors at the same multiplication budget remain unanswered. No first-discovery or novelty claim is made. Cheon, Kim and Kim (2020) retain credit for constant-factor asymptotically optimal composition complexity; their global Lemma 3 combined with the classical degree bound already yields the uniform order by a short synthesis. Chen and Chow (2014) introduced the scaled cubic and endpoint recurrence. Polar Express gives the same centered cubic and optimality within its composition class. The explicit $T_{\min}\le m$ comparison is what this self-contained note supplies. Precise primary locators and the prior-estimate synthesis are in [the source review](verification/source-review/REVIEW.md).

## Authorship and review provenance

The manuscript was developed with substantial ChatGPT/Codex assistance under the author's instructions. The coordinating agent developed the mathematical candidate; agent `/root/review_aa01` prepared the publication conversion. The reviews are distinct:

- [Independent full mathematical and exact-target audit](verification/independent-review/MF-02-independent-review.md), by `/root/prepare_manuscripts`: PASS for the theorem and canonical uniform asymptotic-order target; the broader exact optimization remains partial. The adjacent [manifest](verification/independent-review/manifest.json), frozen inputs, independent standard-library checker and its output are unchanged.
- [Independent source, prior-art and scope audit](verification/source-review/REVIEW.md), by `/root/review_md03_md04`: supports a carefully attributed canonical resolution/status correction; supplies the prior uniform-order synthesis and does not certify novelty. Its [manifest](verification/source-review/source-review-manifest.json) and signed report are unchanged.
- The [independent final conversion addendum](verification/independent-conversion/MF-02-conversion-review.md), by `/root/prepare_manuscripts`, independently confirms all six final hashes, 166 proof formulas, 15 canonical formulas and the declared scope paragraph.
- The [coordinating publication-conversion review](verification/coordinating-conversion-review.md), by `/root`, confirms the final source preservation, all seven rendered pages, author metadata and publication scope. The coordinator contributed to the proof and is not counted as its independent mathematical reviewer.

These are informal automated-agent audits, not external human peer review or formal verification. Finding no mistake does not constitute a proof certificate.

## Preserved sources and conversion

The [original candidate](verification/reviewed-proof.md), also retained as [RESULT.md](verification/RESULT.md), is exactly 11,177 bytes with SHA-256 `63d6a0dccebaf43b7da3dc6b2615755c3c3d24791a12527007f1276256e89ba9`. The original canonical source is retained as [canonical-target.md](verification/canonical-target.md), SHA-256 `1312362ce7bbe162adba3b9305acd2f8cd31dd7d8c8d056ce0138c0b25243127`.

[Editorial conversion evidence](verification/editorial-conversion.json) records the sole scope-paragraph revision inside Sections 1-5. It replaces pending scope review with the completed, explicitly limited canonical conclusion. Reversing that paragraph and removing five page-layout directives recovers the entire original 8,725-byte core, SHA-256 `0c2a3001bcb1d88c2d82ed132161e8ad479fe1c9ea0485445b39dfd7cf3c89a1`. All 166 ordered mathematical expressions are identical in the original candidate, publication Markdown and standalone TeX. Front matter and Section 6 add author metadata, finalized primary attribution and review evidence; the reference correctly uses G. Lorentzon. The [frozen-artifact record](verification/frozen-artifacts.json) binds all six canonical outputs. No proof step was changed during conversion.

Third-party PDFs, source-page images, extracted source text and unredacted network bodies remain private. Their fingerprints and citation locators are retained in the source-review manifest; their absence from this archive is intentional. All PDFs distributed here are repository problem pages or the author's own proof note.

## Bounded public eligibility audit

The [final broader public-network audit](verification/final-public-audit/README.md), completed at **2026-09-12 02:10:34 UTC**, rechecks all five repositories and 40 heads, 108 selected text blobs and all PR-review bodies. Every MF-02 page remains Open, including upstream main at the publication base. No competing resolution was located. The record distinguishes the separate MF-02 prior-publication synthesis from public branch eligibility.

The [sanitized network record](verification/network-check.json), identical to the [source review's record](verification/source-review/network-check-sanitized.json), was completed at `2026-09-12T01:47:54.300055+00:00`. It includes five public repositories, all 40 branch heads, 106 selected text-blob fingerprints and 32 pull-request review bodies read. Every canonical MF-02 page was Open, and no matching solution discussion was found. The search is bounded to the recorded public network, paths and discussion endpoints; it is not an exhaustive priority certificate.

The source review preserves its [original audit script](verification/source-review/network_check.py) unchanged. A [portable read-only adaptation](verification/network_check.py) finds GitHub CLI through `GH` or `PATH`, reads the registry relative to this checkout, takes a required private output path, and checks downloaded Git blob identities. It makes no public changes. Its output contains full source bodies and should remain private; only a sanitized eligibility record should be redistributed.

## Reproduction and document checks

From the repository root:

```bash
python3 references/stepaniants-mf02-2026-09-12/verification/independent-review/exact_algebra_check.py --output /tmp/mf02-exact-check.json
python3 references/stepaniants-mf02-2026-09-12/verification/check_submission.py
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/validate_problem_ids.py --base-ref 1f22006bdaa4659fcaa0bb775a887685cd3cc566
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
python3 -m unittest discover -s tests -p 'test_problem_statuses.py' -v
python3 tools/render_solutions.py MF-02
python3 tools/render_problems.py MF-02
```

The renderers use Pandoc and XeLaTeX, with optional `PANDOC` and `XELATEX` overrides. Each exported TeX file is standalone and was compiled twice. The [document-check record](verification/document-checks.json) gives actual results and all-page visual QA; the [source-check output](verification/source-check-output.json) reports exact source and target preservation. The [fresh exact-check output](verification/exact-check-rerun.json) confirms all 17 supplementary algebra checks. These finite checks support the reviewed analytic proof; they do not establish the all-parameter theorem on their own.
