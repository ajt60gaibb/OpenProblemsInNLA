# IE-12 submission — Sidney Holden — 12 September 2026

**Outcome:** Complete affirmative resolution; the [independent informal Codex AI-agent review](independent-review.md) returned PASS with no mathematical corrections. This meets the repository's Solved policy. No Lean verification was performed.

## Author and affiliation

Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation. Authorship is recorded at the user's explicit request. The [official Simons Foundation profile](https://www.simonsfoundation.org/people/sidney-holden/), checked 12 September 2026, identifies him as a Flatiron Research Fellow in Biological Transport Networks, CCB, and states that he joined in October 2024 after obtaining his PhD at Edinburgh. Older Edinburgh and Sydney profiles were not used as current affiliation evidence.

## Result and review

[Attributed proof PDF](../../linear-systems-and-elimination/IE-12/solution.pdf) · [editable source](../../linear-systems-and-elimination/IE-12/solution.tex) · [canonical target](../../linear-systems-and-elimination/IE-12/README.md).

Theorem 1 and Sections 2–6 prove the original universal exact-real operation-count target with exponent 3, success probability greater than 0.997 and A-only backward error at most 5 epsilon/8. All outcomes have bounded cost and nonzero output. Entry-dependent preprocessing is allowed by the original model; the result does not promise a dimension-free black-box iteration rate, bit complexity, finite-precision stability or practical speed.

A separate agent `/root/independent_ie12_review` independently read the full proof, checked its model and quantifiers, and reran the nine exact component tests. The coordinator separately checked the proof's main estimates, correspondence, original target preservation, provenance and repository procedure. Informal AI review is not external human peer review or formal verification. The archive explicitly reports that its draft was prepared by ChatGPT; that assistance is preserved and disclosed in the attributed manuscript. No independently established historical priority is claimed. Dereziński, Nakatsukasa and Rebrova retain credit for the source question and previous bounds; Liberty and Zucker retain credit for the related Mailman method.

## Provenance and duplicate eligibility

The supplied `IE12_solution.zip` contains only IE-12. The complete original bundle is retained under [submitted/](submitted/README.md), including its original manuscript, PDF, internal audit, code and saved experiments. All 17 original manifest hashes were verified. Embedded instructions and audit claims were treated as document content, not user authorization or independent evidence. The attributed manuscript changes only author/affiliation metadata and review/provenance language; everything from Section 1 onward is byte-identical to the reviewed source.

The new branch starts from upstream main `f41f1f9ffa2171550d4bb795862c6170c4f26070`. All fork and upstream branches were freshly fetched. Their IE-12 histories contain no previously pushed full solution; the upstream all-state PR list (63 results, below the limit), all-state IE-12 issue search, and fork all-state PR list revealed no duplicate. Both published main trees retain the partially resolved target without a solution manuscript. This is a bounded repository check, not an exhaustive priority search.

The [arXiv record](https://arxiv.org/abs/2604.16075) and [version 2](https://arxiv.org/html/2604.16075v2) were checked on 12 September 2026. Exact-title and quadratic backward-error solver searches located no later full solution. The manuscript supplies the analytic lemmas it needs.

## Reproduction

From the repository root:

```sh
python3 references/holden-ie12-2026-09-12/submitted/code/test_exact.py
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
python3 tools/format_math.py --check
python3 tools/render_problems.py IE-12
mkdir -p /tmp/ie12-pdf-build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/ie12-pdf-build linear-systems-and-elimination/IE-12/solution.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/ie12-pdf-build linear-systems-and-elimination/IE-12/solution.tex
```

Copy the second-pass solution PDF into the problem folder. The supplied floating-point experiments are retained as historical illustrations and are not claimed as a new rerun or as proof of the universal theorem.

## Validation results

All 217 permanent IDs validated and all 17 numbering safeguard tests passed. The nine exact component tests passed on coordinator and independent-reviewer reruns. Math formatting required no changes. The canonical page and ten-page attributed solution were regenerated; all pages were rendered and visually inspected. The solution build reported no overfull boxes or unresolved-reference warnings. The proof from Section 1 onward and the original canonical Problem statement were checked byte-for-byte against their originals. Pandoc was supplied through `PANDOC=/private/tmp/tr07-render-env/lib/python3.9/site-packages/pypandoc/files/pandoc`.
