# Sources and dependencies

## Repository formulation

**Open Problems in Numerical Linear Algebra.** “RA-14 — Optimal query complexity of spectral rank-k approximation.”

- Web page: https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/randomized-and-low-rank-approximation/RA-14
- Raw statement: https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/main/randomized-and-low-rank-approximation/RA-14/README.md
- Used for the exact two-sided oracle model, the 0.99 pointwise success requirement, and the requirement of simultaneous universal-factor bounds in n, k, and epsilon.
- Retrieved from the website. No GitHub connector was used; no repository mutation was performed.

## Imported finite-dimensional spectral theorem

**Mark Rudelson and Roman Vershynin.** “The smallest singular value of a random rectangular matrix.” *Communications on Pure and Applied Mathematics* 62 (2009). arXiv:0802.3956v4, 3 August 2009.

- Record: https://arxiv.org/abs/0802.3956v4
- PDF: https://arxiv.org/pdf/0802.3956
- HTML: https://arxiv.org/html/0802.3956
- Exact location: Theorem 1.1, printed page 3, equation (1.10).
- Dependency: Theorem 8.1 in the new manuscript is its standard-Gaussian specialization. All fixed rectangular dimensions are allowed. The manuscript states the formula and the constants it needs. The theorem's original proof is not reproduced.
- The arXiv HTML rendering contains a later generated date. The bibliographic date here is the actual version date above, not that rendering date.

## Antecedent methodology, not an imported RA-14 lower bound

**Mark Braverman, Elad Hazan, Max Simchowitz, and Blake Woodworth.** “The gradient complexity of linear regression.” COLT 2020; arXiv:1911.02212v3, 23 May 2021.

- Record: https://arxiv.org/abs/1911.02212v3
- HTML: https://arxiv.org/html/1911.02212v3
- Proceedings: https://proceedings.mlr.press/v125/braverman20a.html
- Used to acknowledge Wishart Schur-complement conditioning in adaptive matrix-vector lower bounds.
- This package does not infer RA-14's output guarantee directly from that paper's eigenvalue or eigenvector objectives. Its singular completion, determinant tilt, posterior kernel law, and Grassmann estimate are written out in the new manuscript.

## Earlier generated research notes

The v4 PDF and ZIP are copied byte-for-byte into `prior/`. Its ZIP preserves the v3 and original notes. These are unreviewed research artifacts, not published primary literature.

- Original note: *RA-14: Bounds and a spectral-to-PCA reduction.* Source of the charged warm-start construction, re-proved in Appendix A.
- Continuation v3: *RA-14: A Dimension-Sensitive Upper Bound and Lower-Bound Audit.* Source of the upper-bound construction, reproduced in Appendix B.
- Continuation v4: *RA-14: Adaptive Lower Bounds and the Fixed-Accuracy Characterization.* Supplies the preceding state of the project. The new proof does not use its deformed-Wigner concentration theorem or near-critical information argument as a black box.

Only source records, attribution, and precise dependency notes are added here. External research papers are not redistributed in this folder. No source is cited as establishing the still-unresolved all-parameter matching characterization.
