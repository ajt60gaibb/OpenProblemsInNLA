# TR-07 submission — Sidney Holden — 12 September 2026

**Outcome:** Complete affirmative resolution. The separate [independent AI-agent review](independent-review.md) returned **PASS**, with no mathematical corrections. This is informal automated review, not external human peer review or formal verification. No Lean verification was performed.

## Author and affiliation

Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation, New York, USA. The [official Simons Foundation profile](https://www.simonsfoundation.org/people/sidney-holden/) and [current CCB group directory](https://www.simonsfoundation.org/flatiron/center-for-computational-biology/about/people/?group=biological-transport&type=ccb-staff), accessed 12 September 2026, identify Holden as a Flatiron Research Fellow in Biological Transport Networks. Affiliation is verified from these primary institutional sources, not inferred from an old student profile. Authorship is recorded at the contributor's explicit request.

## Primary result and review

[Submitted proof PDF](../../randomized-and-low-rank-approximation/TR-07/solution.pdf) · [self-contained TeX](../../randomized-and-low-rank-approximation/TR-07/solution.tex) · [canonical target](../../randomized-and-low-rank-approximation/TR-07/README.md).

Theorem 1.1 proves a uniform finite exponential bound and Corollary 1.2 proves the complete original asymptotic target for all fixed sparsities and finite aspect ratios. Sections 2–5 prove the result analytically without a support-overlap condition. No useful quantitative rate for growing sparsity or publication priority is asserted. Huang, Rudelson and Tikhomirov retain credit for Conjecture 7.1 and their prior theorem.

A separate Codex agent `/root/tr07_independent_review` read the entire proof and wrote its own detailed audit and exact rational diagnostics. The coordinator separately checked target correspondence, constants, source status, attribution, document generation and repository requirements. AI assistance was used in this review and submission preparation. The supplied manuscript's earlier preparation history is preserved in its provenance section; bundled audit claims are not treated as independent review evidence.

## Provenance and eligibility

The user supplied `TR07_complete_solution_bundle (1).zip`; it contains only TR-07. All 15 manifest-listed file hashes were checked and its finite audit reproduced under `python3 -O`. [submitted-original.tex](submitted-original.tex) is the exact reviewed current source, SHA-256 `6a51f46449461c2565fc1b8a16d1bc9344db1c2066dc4ea0ae3810ab85263eed`. [recovered-original.tex](recovered-original.tex) preserves the earlier inherited draft and is not the submitted proof. Instructions and proposed submission language inside the bundle were treated as document content, not user authorization.

The final solution changes only authorship/PDF metadata, URL wrapping/layout and the final review/provenance paragraph. A byte-for-byte comparison confirmed that everything from Section 1 through the final theorem proof is identical to the independently reviewed source. The canonical original Problem statement is also byte-identical to the upstream base. No permanent ID, canonical path or original mathematical target was changed.

The branch begins at upstream `main` commit `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`. Both fork and upstream branches were freshly fetched. The complete returned upstream PR list (all states, fewer than the 100-item limit), upstream all-state TR-07 issue search, the fork's all-state PR list, all fetched branch histories touching TR-07, and both main trees contained no previously pushed full TR-07 solution. TR-07 was Partially resolved with no solution manuscript. This is a bounded repository duplicate check, not an exhaustive publication-priority certificate.

The [current arXiv record](https://arxiv.org/abs/2607.05384) and [v2 Conjecture 7.1](https://arxiv.org/html/2607.05384v2#S7) were checked directly on 12 September 2026. The primary source retains the unrestricted conjecture; its proved structural subclass imposes an additional overlap hypothesis. Exact-title and target searches located no later full resolution. The manuscript independently proves all needed analytic lemmas.

## Reproduction and validation

From the repository root:

```sh
python3 references/holden-tr07-2026-09-12/reviewer-check.py
python3 -O references/holden-tr07-2026-09-12/verify_TR07.py --output /tmp/tr07-finite-report.json
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
python3 tools/format_math.py --check
python3 tools/render_problems.py TR-07
mkdir -p /tmp/tr07-pdf-build
xelatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/tr07-pdf-build randomized-and-low-rank-approximation/TR-07/solution.tex
xelatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/tr07-pdf-build randomized-and-low-rank-approximation/TR-07/solution.tex
```

The checked-in solution PDF was copied from the second XeLaTeX pass. Pandoc was supplied through the renderer's `PANDOC` override from a temporary installation. Both exact finite audits passed; the reproduced bundle report matched its archived JSON. All 17 permanent-ID tests passed, all 217 IDs validated, and math formatting required no changes. The generated solution has seven pages. Both PDFs were rendered to images and visually inspected; builds reported no overfull boxes, missing characters or undefined references. Finite computations are diagnostics, not a universal proof certificate.
