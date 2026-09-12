# MF-18 resolution by George Stepaniants

**Result:** the complete complex-coefficient imaginary-part rank equality in MF-18, proved in Theorem 1 and Sections 1-4 of the [manuscript](../../matrix-functions-and-stability/MF-18/solution.md). [PDF](../../matrix-functions-and-stability/MF-18/solution.pdf) · [standalone TeX](../../matrix-functions-and-stability/MF-18/solution.tex) · [canonical problem](../../matrix-functions-and-stability/MF-18/README.md).

## Author and attribution

George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. The name and affiliation are published with his authorization. His department and university were checked against his [official Caltech profile](https://www.cms.caltech.edu/people/george-stepaniants) on 11 September 2026. No contact email is included.

The proof was developed with substantial ChatGPT/Codex assistance at the author's request. One agent constructed the full proof, the coordinating agent independently reconstructed and simplified the key algebra, and a third agent performed the complete adversarial mathematical review. The [independent report](verification/MF-18-independent-review.md) returned **PASS** for the full canonical complex target. It checks singular coefficients, simple roots at 1 and -1, the zero-boundary-root case, and arbitrary strictly stable Jordan blocks.

Guo, Kuo, and Lin retain credit for the problem, the known upper bound, and the earlier real-coefficient result. Matthew J. Colbrook retains credit for the repository's distinct auxiliary real-coefficient theorem involving defective unit-circle structure. That auxiliary theorem is not an assumption of this proof. Its manuscript, review, and original scope remain intact.

This verification is independent automated-agent review, not external human peer review, formal proof-assistant verification, or certification of historical priority. The finite nonsingular stabilizing limit remains an assumption. The proof retains algebraic simplicity of the unit-circle roots and makes no new assertion for defective roots.

## Exact reviewed source and publication conversion

The archived [frozen proof](verification/reviewed-proof.md) has 10,665 bytes and SHA-256 `dc6fb4b1b4c8d1fc2d841b35165e708d21d8f228dfdf18402e5845a9f29fcfd7`. Its original pre-review status wording is retained as provenance. The independent report has 9,200 bytes and SHA-256 `3c4f41e34a1ea41351e49f865ef26ff3c77d38e5213ffcddce4c370502a11011`; it binds its verdict to the frozen short version, not to the earlier exploratory draft.

The published manuscript copies the complete mathematical body, from Theorem 1 through the end of Section 4, **byte for byte** (7,900 bytes). Only publication metadata, the completed audit/review description, and two repository reference URLs outside that body changed. No theorem, equation, assumption, argument, or mathematical conclusion was altered in conversion. The [document checks](verification/document-checks.json) record source identity and build results.

The independent report includes exact scalar and block-diagonal sanity checks. No numerical search or finite computation is used as evidence for the general theorem. The proof uses standard finite-dimensional spectral facts, the argument principle, and Rouché's theorem.

## Existing-solution check

The [public-network snapshot](verification/network-check.json), completed at **2026-09-11 22:37:32 UTC**, checks the original repository, its network source, every recursively reported public fork, and all public branch heads: **five repositories and 29 heads**. Every canonical MF-18 page retained **Partially resolved** status. The check also fetched ID-named and relevant nano/Green/Riccati/imaginary text documents and root indexes, and checked issues, PR bodies, issue comments and inline review comments in every repository.

The only matching discussions were [the earlier auxiliary report #45](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/45), [PR #47](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/47), and its review-request comment. Their stated scope leaves the general complex target open. The published snapshot trims unrelated root-index text to MF-18 excerpts while retaining complete-file hashes and the SHA-256 of the complete local fetch. The scope excludes private, deleted, unpublished or unidentifiably named work.

A [final pre-publication recheck](verification/network-before-push.json) at **22:48 UTC** confirmed the same five repositories and 29 public heads, with every MF-18 page still partial and no new full-solution discussion.

A bounded literature check read the [JCAM primary manuscript](https://uregina.ca/~chguo/JCAM_GuoKuoLin.pdf), especially Theorem 5 and its following conjecture, and [Guo's publication list](https://uregina.ca/~chguo/paper.html), and searched the exact title, authors, imaginary-part rank and conjecture. No full general-complex resolution was located. This is evidence about the checked sources, not an exhaustive priority claim.

The portable read-only checker can be rerun using an authenticated GitHub CLI:

```bash
python3 references/stepaniants-mf18-2026-09-11/verification/network_check.py --output /tmp/mf18-network-check.json
```

Set `GH` to the CLI path if it is not on `PATH`.

## Reproduction and repository safeguards

```bash
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/validate_problem_ids.py --base-ref upstream/main
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
python3 tools/render_solutions.py MF-18
python3 tools/render_problems.py MF-18
```

The branch is based on upstream commit `aaa88c40fbf58e8cebc335021b3c5cd108c357e4`. All 203 permanent ID/path mappings and the original canonical mathematical statement are preserved. The shared solution template makes its email field optional. Each generated TeX file compiles independently with XeLaTeX. The proof PDF and canonical PDF are rendered and visually checked in full; final identities and validation results appear in [document checks](verification/document-checks.json).
