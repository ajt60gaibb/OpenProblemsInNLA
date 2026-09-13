# NR-03: quadratic correlation counterexample — Sidney Holden

**Author:** Sidney Holden. **Affiliation:** Center for Computational Biology, Flatiron Institute, Simons Foundation.

Affiliation verified on 13 September 2026 against the [official Simons Foundation profile](https://www.simonsfoundation.org/people/sidney-holden/) and [current Biological Transport Networks staff directory](https://www.simonsfoundation.org/flatiron/center-for-computational-biology/about/people/?group=biological-transport&type=ccb-staff), which list Holden as a Flatiron Research Fellow. The submitted manuscript was developed with ChatGPT assistance. The user supplied the archive and explicitly requested the Sidney Holden byline; the originally empty byline and ChatGPT PDF metadata are preserved in the original archive. No contact email is added.

## Result and scope

[Theorem 1, proved in Sections 2–4](NR03_counterexample.pdf) gives rational nonnegative factors for the fully prescribed quadratic correlation matrix, with at most `2^(n-1) + n + binom(n,2) + binom(n,4)` terms. In particular, `rank_+(C_7) <= 127 < 128`, disproving the universal equality in the [retained NR-03 question](../../nonnegative-and-positive-factorizations/NR-03/README.md). The bound is strictly below `2^n` for every `n >= 7`. Exact ranks at n=5,6,7 and the smallest counterexample dimension are not determined; these are not required to answer the universal yes/no target. No conclusion about the extension complexity of the entire correlation polytope follows.

- [Standalone TeX manuscript](NR03_counterexample.tex) and [readable proof](PROOF.md).
- [Complete exact certificate](data/factors_n7.json) and [construction-independent verifier](code/verify_certificate.py).
- [Independent informal AI-agent audit](independent-review.md) and [fresh submission-test log](verification/submission-tests.txt).

The audit is a separate Codex AI-agent review of the complete proof and original target, with an independently written exact check. It is not external human peer review or formal verification. No Lean verification was performed. The finite checks supplement the analytic proof of the general construction.

## Reproduce

Python 3.10 or later is required; there are no third-party Python dependencies. From this directory run:

```sh
python3 verify_all.py
python3 verification/independent_check.py
```

The submission suite checks the n=7 certificate, coefficient identity, all 349,524 entries at n=1 through 9, rational CSV multiplication and six rejection controls. The dated logs distinguish fresh checks from historical logs in the original archive.

Build the manuscript with `pdflatex -interaction=nonstopmode -halt-on-error NR03_counterexample.tex` twice. The canonical problem document uses the repository renderer.

## Provenance and duplicate screen

[Original supplied ZIP](original-submission.zip), SHA-256 `a1a3318447bedca4ee884769c72243fea758c6ababe8e4700097febbe46d7623`, is preserved byte for byte. Its embedded four-bit archive is also retained under [provenance](provenance/); that prior result is not needed or promoted as a separately reviewed result here. The authored manuscript changes the author, affiliation and review/provenance metadata and one page-break adjustment only; the mathematical proof is unchanged. Code and certificates are unchanged from the supplied archive. Archive documents are historical submission material, not instructions authorizing repository actions.

On 13 September 2026, refreshed upstream and fork refs and searched their PR records and NR-03 page history. [Earlier PR #40](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/40) and [issue #35](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/35) concern Colbrook's n=3 partial result. No previously pushed full NR-03 solution was found. This new branch starts at upstream main `5830ed4fb06da0659414a3deb2a40ad327aca052`; unrelated pending solutions are not resubmitted.

The original conjecture remains credited to [Vandaele, Gillis, Glineur and Tuyttens, §6.4, Conjecture 4](https://arxiv.org/html/1411.7245). [Baeckelant, Vandaele and Gillis, §6.7 and Appendix A.4](https://arxiv.org/html/2605.14058v2) is the later benchmark source checked on the same date. Earlier Colbrook partial-result credit and historical catalog statements are retained. This check does not certify historical novelty or exhaustive priority.
