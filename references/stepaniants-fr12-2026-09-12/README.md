# FR-12 negative resolution - 12 September 2026 (UTC)

**Author:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA.

The [complete proof](../../frames-and-matrix-designs/FR-12/solution.md), Lemma 1 and Theorem 1, disproves the original upper-bound conjecture for labeled real Hadamard matrices. The matching-indexed injection gives

$$
H(2m)\ge(2m-1)!!H(m)^2,
\qquad H(2^k)\ge2^{2^k(k-1)(k-2)/8}\quad(k\ge2).
$$

The second bound contradicts every proposed absolute constant in the original $2^{Cn\log_2 n}$ upper bound. It does not settle existence at every admissible order or provide the optimal asymptotic count. The canonical ID, path, original target, and historical source attribution are retained.

[Proof PDF](../../frames-and-matrix-designs/FR-12/solution.pdf) · [Standalone TeX](../../frames-and-matrix-designs/FR-12/solution.tex) · [Canonical entry](../../frames-and-matrix-designs/FR-12/README.md).

## Supplied source and independent review

The user supplied the [original manuscript](original-user-source.tex) in the conversation. Its SHA-256 is `efbcaeb82adc140be98cdffca39bf9d9a34d3b281951f42c9d7f7232279335ba` (7,123 bytes). The separate [independent Codex-agent audit](REVIEW.md) returned PASS for the entire negative proof and its match to published Conjecture 1.3. It reconstructs the decoder, collision argument, all-order recurrence, and contradiction for every fixed constant. No mathematical correction was requested.

The reviewer's identical source copy is [reviewed-proof.tex](reviewed-proof.tex); the frozen [canonical target](canonical-target.md) is from upstream main `1f22006bdaa4659fcaa0bb775a887685cd3cc566`. The [independent manifest](independent-manifest.json) binds the review and its supporting files. Navigation in that frozen target is historical; use the live canonical-entry link above.

The public TeX retains the entire supplied body from `\section{Exact target}` through the bibliography byte-for-byte. Changes concern the author, affiliation, date, and accurate assistance/review disclosure. The [source-preservation record](source-preservation.json) contains the exact difference, retained-body hash, and Markdown formula comparison. The supplied source's original pending-review paragraph is historical and is superseded by the signed PASS report.

Substantial AI assistance is disclosed. This independent automated-agent audit is informal review, not external human peer review, formal verification, or a historical priority certification.

## Attribution and eligibility

Ferber, Jain and Zhao retain credit for the original conjecture and quadratic-exponent upper bound. The proof's counting convention agrees with the definition and Conjecture 1.3 on printed page 456 of their [published paper](https://doi.org/10.1017/S0963548321000377). The classical use of doubling to construct Hadamard matrices is also discussed in [the 2007 doubling paper](https://combinatorialpress.com/jcmcc-articles/volume-063/inequivalent-hadamard-matrices-of-order-2n-constructed-from-hadamard-matrices-of-order-n/); this submission's reviewed assertion is the labeled injection count and its iteration.

The [public-network audit](public-audit/README.md) inspected six public repositories and 49 branch heads at 04:45:40 UTC on 12 September 2026. A [refresh at 04:57:52 UTC](public-audit/head-refresh.json) confirmed the same 49 heads and upstream main. All 19 heads containing FR-12 retained Open status; the other 30 did not contain the page. Selected source documents, issue/PR/comment bodies, and all returned PR-review bodies yielded no competing full resolution. The [source-search notes](source-search.md) record the mathematical source check and limits of the later-work search. Private, deleted, unpublished, unidentifiably named, and later work are outside this bounded check.

## Reproduction

From the repository root, run:

```sh
python3 references/stepaniants-fr12-2026-09-12/verify_fr12.py --source references/stepaniants-fr12-2026-09-12/original-user-source.tex
python3 references/stepaniants-fr12-2026-09-12/independent_check.py
python3 references/stepaniants-fr12-2026-09-12/build_solution.py
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/update_catalog.py --base-ref origin/main
python3 tools/render_problems.py FR-12
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
python3 -m unittest discover -s tests -p 'test_problem_statuses.py' -v
```

The two mathematical checkers use only the Python standard library. The separately written reviewer checker additionally covers 26,880 outputs over a specified order-four input sample and every matching, plus exact recurrence checks through $k=12$. Its [saved output](independent-check.json) identifies that finite scope. The packaging checker reproduces the manuscript's two complete small-order tables and recurrence inequalities through $k=10$; its output is [verification-output.json](verification-output.json). These computations supplement the analytic proof and do not establish its universal quantifiers by enumeration.

The proof builder uses XeLaTeX; the canonical renderer also requires Pandoc. Set `XELATEX` and `PANDOC` when those executables are outside PATH. Both exported TeX sources are standalone. The separate [publication-package audit](packaging-review/REVIEW.md) checks preservation, conversion, document text/privacy, and evidence bindings. The final [verification record](verification.json) and [manifest](manifest.json) record document, source-preservation, privacy, permanent-ID, and required-test evidence separately from the mathematical review.

`Solved` is proposed under the repository's independent-informal-audit rule. Upstream inclusion requires maintainer review and merge of the linked new pull request.
