# IE-16 submission - Sidney Holden - 12 September 2026

Author: **Sidney Holden**, Center for Computational Biology, Flatiron Institute, Simons Foundation. Authorship was added at the contributor's explicit request. The [official institutional profile](https://www.simonsfoundation.org/people/sidney-holden/) and [CCB directory](https://www.simonsfoundation.org/flatiron/center-for-computational-biology/about/people/?group=biological-transport&type=ccb-staff), checked 12 September 2026, identify Holden as a Flatiron Research Fellow in Biological Transport Networks.

The [publication manuscript](../../linear-systems-and-elimination/IE-16/solution.pdf) and [source](../../linear-systems-and-elimination/IE-16/solution.tex) contain the submitted mathematics, with only author, affiliation, date and PDF metadata added. The unchanged supplied bundle is retained under [submitted](submitted/README.md). Instructions inside that bundle were treated as document content, not user authorization. Liesen and Tichy retain attribution for the original conjecture and prior results.

The separate [independent Codex AI-agent review](INDEPENDENT-REVIEW.md) covers the finite counterexample and stronger amplification theorem. This is informal AI review, not external human peer review or formal verification. AI assistance was used for review and submission preparation. No Lean verification was performed. The nine-point counterexample alone negatively resolves the original universal inequality; the stronger theorem is not needed for that status.

## Duplicate and source check

Started from freshly fetched upstream main at `f41f1f9`. IE-16 was Partially resolved and had no solution manuscript. Checked all returned upstream PRs (all states, limit 300), fork PRs, upstream IE-16 issues, local histories and published fork branch names: no prior full IE-16 submission was found. This is a bounded repository duplicate check, not an exhaustive novelty claim. The original primary paper, Section 3.2.2, conjecture (3.16), was checked at its author-hosted URL on 12 September 2026.

## Reproduction

From the repository root:

```sh
python3 references/holden-ie16-2026-09-12/submitted/code/verify.py --output /tmp/ie16-certificate
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
python3 tools/format_math.py --check
python3 tools/render_problems.py IE-16
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp linear-systems-and-elimination/IE-16/solution.tex
```

Run the final PDF compilation twice to resolve cross-references. The verifier uses exact rational arithmetic and checks all 126 five-point subsets; it does not certify the general amplification theorem.

Original archive SHA-256: `a268b5dd4ccbe557f529582149d8ab31b8d9637c6983af4974ddb03e00198608`.

## Completed validation

The independent audit passed both the finite counterexample and the stronger theorem. All 217 permanent IDs validated and all 17 safeguard tests passed. Catalogs and the canonical TeX/PDF were regenerated; repository math formatting passed. The original mathematical target is byte-identical to upstream main, and the reviewer confirmed the publication mathematics is byte-identical to the supplied source. The nine-page solution and two-page problem PDF were rendered and visually inspected with no clipping or overlap; the final manuscript compilation reported no warnings.
