# Primary sources and provenance

Access date: 12 September 2026 (America/New_York). Public website/raw-file access only; no GitHub plugin. This was a targeted, multi-pass mathematical investigation, not an exhaustive bibliographic survey.

## Exact target and reporting rules

1. OpenProblemsInNLA, NM-01 canonical entry. Source for the weak orthogonal-cone SSC convention, rational input, column normalization, unrestricted signs of W, hidden factors, bit complexity, randomized success requirement, and exclusion of promise checking.
   https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/main/nonnegative-and-positive-factorizations/NM-01/README.md
2. OpenProblemsInNLA, contribution guidelines. Source for preserving the displayed target and distinguishing partial results, informal audits, and formal verification.
   https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/main/CONTRIBUTING.md

## Factorization and convex-geometric context

3. M. Abdolali and N. Gillis, *Simplex-Structured Matrix Factorization: Sparsity-based Identifiability and Provably Correct Algorithms*, arXiv:2007.11446. Facet identification and rank conditions; background also used in the first round.
   https://arxiv.org/abs/2007.11446
4. C.-H. Lin, R. Wu, W.-K. Ma, C.-Y. Chi, and Y. Wang, *Maximum Volume Inscribed Ellipsoid: A New Simplex-Structured Matrix Factorization Framework via Facet Enumeration and Convex Optimization*, arXiv:1708.02883v3. The supplied-facet convex framework does not itself remove facet enumeration from vertex-described inputs.
   https://arxiv.org/html/1708.02883v3
5. N. Gillis, *Nonnegative Matrix Factorization*, SIAM, 2020. The canonical entry identifies Definitions 4.15 and 4.42, Theorem 4.43, and Section 4.3.3.6. This locator is credited through the canonical entry; this round does not claim a fresh full reading of the book.
   https://doi.org/10.1137/1.9781611976410
6. G. Barbarino, N. Gillis, and S. Saha, *Robustness of Minimum-Volume Nonnegative Matrix Factorization under an Expanded Sufficiently Scattered Condition*, arXiv:2511.04291v1. Section 5 discusses polynomial solvability; robustness given a global optimum is not an algorithm for finding it.
   https://arxiv.org/html/2511.04291v1
7. N. Gillis and R. Luce, *Checking the Sufficiently Scattered Condition using a Global Non-Convex Optimization Software*, arXiv:2402.06019; IEEE Signal Processing Letters 31 (2024), 1610–1614. Its promise-checking problem is not NM-01.
   https://arxiv.org/abs/2402.06019

## Algebraic and SOS ingredients

8. A. K. Lenstra, H. W. Lenstra Jr., and L. Lovasz, *Factoring polynomials with rational coefficients*, Mathematische Annalen 261 (1982), 515–534. Standard polynomial-time rational univariate factorization theorem. Bibliographic details and original publication landing page were verified; the publisher preview did not supply the complete text in this round.
   https://link.springer.com/article/10.1007/BF01457454
9. K. Kellner and T. Theobald, *Sum of Squares Certificates for Containment of H-polytopes in V-polytopes*, arXiv:1409.5008v4 (2016). Full PDF and a rendered page were checked; Section 4 supplies SOS-containment background. Its precise formulation is not asserted to coincide with every preordering in the new report.
   https://arxiv.org/abs/1409.5008
10. K. Kellner, T. Theobald, and C. Trabandt, *Containment problems for polytopes and spectrahedra*, arXiv:1204.4313v3 (2013). Full PDF and a rendered page were checked. Theorem 3.4 concerns generic H-polytope/ball containment, not an NM-01 promise-preserving reduction.
    https://arxiv.org/abs/1204.4313

## Earlier artifact and new derivations

The original archive is `previous/NM01_partial_results.zip`, SHA-256:
`873c127847eabb255272af6cdccdea8ace902a3c9eac773b4c81c6c8fd69dabe`.
Its rationality/facet-support and exact-bit arguments are explicitly identified as inherited results. The exact reference module is copied unchanged as `code/exact_baseline.py`, SHA-256:
`20729dca7535c36d8822d7910bcbe573c9768734e65d2d630cb178aeb9b34cd7`.

The projective reconstruction argument, diagonal-rigidity construction, off-promise interval certificate, and stated all-degree SOS construction are mathematical derivations developed in this round, with proofs supplied in the report. They are not attributed to the above papers. No claim of exhaustive novelty checking or priority is made. No copyrighted source PDFs or font files are redistributed here.
