# Literature coverage and uncounted leads

Last updated: **2026-09-08**. This records source coverage and consequential
exclusions. It is not an exhaustive bibliography or a claim that every problem
in the books below has been checked. Each admitted entry has its own references
and status evidence in the [catalog](catalog/README.md).

## Books, monographs, and surveys examined

| Source | Material actually examined | Result / next useful work |
| --- | --- | --- |
| N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002; [university-hosted copy](https://pages.stat.wisc.edu/~bwu62/771/hingham2002.pdf) | The user's 20 numbered leads, methodological Problem 26.4, and five prose leads; critical matrix patterns, formulas, and algorithms checked in page images. | Problems 9.15(a–b) and 9.18 supply IE-13–15. The Hadamard part of 9.17 duplicates IE-03. [Full screening](HIGHAM-2002-SCREEN.md) records later results and all uncounted leads. This is a selected-passage screen, not a cover-to-cover review. |
| R. Jungers, *The Joint Spectral Radius: Theory and Applications*, Springer, 2009; [author manuscript](https://perso.uclouvain.be/raphael.jungers/sites/default/files/kcfinder/files/book.pdf) | Strict stability decidability, finiteness, algebraicity, and marginal-growth questions in §§2.2.3, 4.4 and the growth discussion. | MF-04, MF-09, MF-10; later work replacing refuted growth conjectures leads to MF-11–12. |
| M. Bläser, *Fast Matrix Multiplication*, Graduate Surveys 5, Theory of Computing, 2013; [open monograph](https://theoryofcomputing.org/articles/gs005/gs005.pdf) | Arithmetic models and named research problems on addition chains, bilinear rank, direct sums, and asymptotic tensor rank. | AC-01–05 and AC-07–08; direct-sum additivity and a historical rank-complexity question excluded after later results. The monograph is distributed under CC BY. |
| N. J. Higham, *Functions of Matrices: Theory and Computation*, SIAM, 2008; [author's book page](https://nhigham.com/books/) | Problems 3.11 and 6.25, the Newton square-root iteration in §6.8.3, and the scaling-and-squaring forward-error question, checked with the author's errata and follow-up papers. | SF-01 retains the real H-matrix question; Problem 3.11 is resolved. A new quantitative forward-error bound was not silently attributed to the book. Full-book coverage is unfinished. |
| N. Gillis, *Nonnegative Matrix Factorization*, SIAM, 2020; [author-hosted book](https://orbi.umons.ac.be/bitstream/20.500.12907/42337/1/NMFbook_SIAM_reprint.pdf) | Explicit conjectures in §§3.6.3.4, 3.6.5, 3.7, 4.3.3.6–7, 6.1.3–4, together with their definitions and cited primary papers. | NR-01–03, NM-01, and NM-03. Later work supplies NR-04. NM-02 is withheld pending a concrete geometric compatibility check. Minimum-volume models and competing definitions of sufficient scattering must be distinguished. Noise-robustness results from 2025 partly supersede the book's broad direction. |
| J. Demmel, I. Dumitriu, O. Holtz, and P. Koev, *Accurate and efficient expression evaluation and linear algebra*, Acta Numerica 17 (2008), 87–145; [primary precursor](https://arxiv.org/abs/math/0508350) | Arithmetic-model definitions and the accurate-polynomial-evaluation decision question in §§3.1 and 3.3.7, checked against the precursor's computation-tree model and a 2025 author seminar. | AA-01. Stored-value reuse and independent operation errors are specified explicitly. |
| Fawzi et al., [*Positive semidefinite rank*](https://arxiv.org/abs/1407.4095); Berman, Dür, and Shaked-Monderer, *Open problems in the theory of completely positive and copositive matrices*, ELA 29 (2015), 46–58 | Named PSD-rank and completely positive factorization questions, with subsequent exact-rank, rationality, and rigidity papers. | PF-01–04; the August 31, 2026 revision of Dawson et al. supplies PF-05. Interior and boundary rational-factorization statements are different. |
| N. Gillis and P. Sharma, *Solving matrix nearness problems via Hamiltonian systems, matrix factorization, and optimization*; [2022 manuscript](https://arxiv.org/abs/2202.02618) | §3.5.2, read with Fu's precise strict-Hurwitz formulation. | MF-08; unrestricted and constrained feedback must not be conflated. |
| Amsel et al., *Linear Systems and Eigenvalue Problems: Open Questions from a Simons Workshop*; [August 2026 version](https://arxiv.org/html/2602.05394v3) | Individual questions across eigenvalue algorithms, low-rank approximation, embeddings, tensor algorithms, and elimination, with follow-up screening. | Several IE, MF, and TR entries. The August revision records several 2026 solution claims, including the fermionic-kernel question; the report cannot be copied as a current list. |
| Amsel et al., [*Quasi-optimal Hierarchically Semi-separable Matrix Approximation*](https://arxiv.org/html/2505.16937v2); Chen et al., [*Near-optimal hierarchical matrix approximation from matrix-vector products*](https://arxiv.org/abs/2407.04686); Amsel et al., [*Query Efficient Structured Matrix Learning*](https://arxiv.org/html/2507.19290v2) | HSS and HODLR approximation definitions, error/query guarantees, lower-bound regimes, and finite/linear-family questions, including the August 2026 abstract update. | RE-01–03, RE-05–06. The finite-family relative-error improvement is resolved in an author-endorsed update despite a stale question remaining in §5. |
| Adm and Garloff, [*Certification of the Sign Regularity of Matrix Intervals*](https://doi.org/10.1007/s44146-026-00223-y), 2026 | Definitions, vertex tests, and surviving nonsingular sign-regular conjecture in §3, traced to the 2016 survey. | IV-01; the totally nonnegative special case and strictly sign-regular case are already proved. |
| Horáček, Hladík, and Matějka, [*Determinants of interval matrices*](https://doi.org/10.13001/1081-3810.3719), 2018 | Journal §5.4 and its H-matrix special case, compared with 2023 symbolic tridiagonal algorithms. | IV-02; the later algorithms use a different generalized interval multiplication and do not compute the exact independent-entry range. |
| E. N. W. Epperly, [*Make the Most of What You Have*](https://tropp.caltech.edu/dissertations/Epp25-Making-Most.pdf), Caltech dissertation, 2025 | §11.1 conjectures and §§20.1–20.3 research directions, followed through January and August 2026 papers. | RA-02 survives; later papers supply RA-01 and RA-03. Dissertation Conjectures 11.1 and 11.3 are covered by the August paper. Qualitative estimation/downdating directions remain uncounted. |
| Hladík et al., [*An overview of absolute value equations: from theory to solution methods and challenges*](https://doi.org/10.1007/s10589-025-00717-5), 2026; Hladík, [*Absolute value equations with $2^n$ solutions*](https://doi.org/10.1007/s11590-025-02251-z), 2026 | Exact solution-count recognition, diagonal-perturbation conditioning, and regularity-promised algorithms, traced to the condition-number paper and P-LCP literature. | AV-01–03. Later uniqueness work and an inaccessible rectangular-system paper remain uncounted rather than reconstructed from abstracts. |

## Important historical questions excluded

Chapter-local exclusion lists give further detail. “Proof claim” below means
that a primary manuscript claims a resolution; this project has screened the
scope of the claim, not independently proved its correctness. Such questions
are withheld from an open collection while the claim stands.

| Historical question | Later evidence | Consequence |
| --- | --- | --- |
| General Crouzeix constant-two conjecture | Lorist and Schwenninger, [*A solution to Crouzeix's conjecture*](https://arxiv.org/abs/2608.03841), August 2026 preprint. | Withheld because of a full proof claim. |
| Polynomial worst-case element growth with complete pivoting | Shah and Urschel, [*Entry growth in Gaussian elimination*](https://arxiv.org/abs/2608.19189), August 2026 preprint. | Claimed quasipolynomial lower growth rules out the old polynomial conjecture. Distinct structured and small-order questions remain in IE. |
| Forsythe conjecture, all restart lengths | Colbrook, Stepaniants, and Townsend, [*A Complete Resolution of Forsythe's Conjecture for Restarted Conjugate Gradients*](https://arxiv.org/abs/2609.04659), September 4, 2026, Theorem 1.1. | IE-01 removed: convergence for $s=3$, counterexamples for every $s\ge4$. The earlier screen missed this resolution. |
| Growth factor at most two for complex symmetric matrices with positive definite real and imaginary parts | Drury, [2013 determinant inequality](https://doi.org/10.1016/j.laa.2013.08.031); Teng Zhang, [2026 refinement](https://arxiv.org/abs/2604.23024). | Higham's ASNA Problem 10.12 is historical, not an open entry. Earlier author/link errors are corrected in the Higham screen. |
| Jordan form of the Fréchet derivative of a matrix function | Noferini, [*The Jordan canonical form of the Fréchet derivative of a matrix function and the bivariate Jordan problem*](https://arxiv.org/html/2512.08399v5), §§4–5, and [journal record](https://doi.org/10.1016/j.laa.2026.06.002). | Higham's Functions of Matrices Problem 3.11 is answered. The paper leaves different structural questions open. The journal issue is dated October 2026, but the manuscript and online result were available before this check. |
| Matrix Spencer discrepancy conjecture | Akbas and Sra, [August 2026 manuscript](https://arxiv.org/abs/2608.28816). | Withheld because of a claimed general constructive result; earlier partial results are no longer an adequate status check. |
| Tensor-rank direct-sum additivity | Shitov, [*A counterexample to Strassen's direct sum conjecture*](https://arxiv.org/abs/1712.08660). | Refuted; not interchangeable with AC-05. |
| Finiteness for pairs of binary matrices of order three | Mejstrik, [2025 manuscript](https://arxiv.org/abs/2505.10178). | Proved special case; MF-04 retains the all-dimensions rational question. |
| Logarithmic cutoff dependence for greedy cross approximation of the fermionic kernel | The [August workshop revision](https://arxiv.org/html/2602.05394v3), Problem 4.2, reports Pendyala's full proof claim. | Former TR-02 withheld. This exclusion relies on the workshop update; the cited proof itself was not independently reviewed. |
| Relative-error least squares and SVD from oblivious subspace injection alone | Townsend and Wang, [*Oblivious Subspace Injection Is Not Enough for Relative Error*](https://arxiv.org/html/2604.10215v2), §§3.1 and 4.1; August 2026 revision. | Counterexamples resolve the historical general implications negatively. Source section locators were checked directly. |
| Nyström diminishing returns for SDDM/SDD inverses | Colbrook, [July 2026 manuscript](https://arxiv.org/abs/2607.19282). | Positive SDDM theorem and an SDD counterexample exclude both historical questions. |
| Finite-family structured approximation with relative error $1+\varepsilon$ and about $\sqrt{\log|\mathcal F|}$ queries | Amsel et al., [August 2026 abstract update](https://arxiv.org/html/2507.19290v2), with an author-endorsed human-verified argument. | Former RE-04 excluded. The linear-family and nonadaptive questions remain distinct. |
| Higham's historical Aasen growth upper bound | Feng and Lu, [*On the growth factor upper bound for Aasen's algorithm*](https://arxiv.org/abs/1805.08994v2), Applied Mathematics Letters 88 (2019), 118–124. | The old $4^{n-2}$ bound is replaced by $2^{n-1}$; exact sharp growth in larger orders needs a new, fully specified pivoting question and separate status check. |
| RPCholesky dissertation trace/spectral oversampling conjectures 11.1 and 11.3 | Epperly, [*A new analysis of the randomly pivoted Cholesky algorithm*](https://arxiv.org/html/2608.20633v1), August 21, 2026, Corollary 1.3 and Theorem 1.4. | The old versions are excluded. RA-01 asks for the sharper pivot bound explicitly conjectured in the new paper. |

## Uncounted source leads requiring further work

The [Higham 2002 screening note](HIGHAM-2002-SCREEN.md) gives dispositions,
references, and admission obstacles for all supplied book leads. In particular,
the old CGS question has a later answer, the Sylvester question has a September
2026 partial answer, and Sherman–Morrison bounds remain a promising candidate
whose complete arithmetic model needs clarification.

- **Inverse estimates for row-diagonally-dominant matrices.** Higham ASNA
  Problem 15.8, printed p. 304, and [Higham 1990](https://eprints.maths.manchester.ac.uk/354/1/0611036.pdf),
  §4, concern the maximum of
  $\|\,|U^{-1}|\,|L^{-1}|y\|_\infty/\|\,|A^{-1}|y\|_\infty$ for real
  row-diagonally-dominant $A=LU$ and $y\ge0$. A precise formulation must require
  nonsingularity, nonzero leading pivots, and $y\ne0$. The original tridiagonal
  bound is $2n-1$ and a dimension-independent improvement was conjectured;
  the book asks about full matrices. Huang, Liu, and Zhu's
  [2014 publisher abstract](https://link.springer.com/article/10.1007/s10543-014-0481-5)
  explicitly claims to settle the tridiagonal conjecture. Its full theorem was
  not retrieved, so no exact constant or full-matrix extension is asserted.
  The narrower conjecture is withheld; the full-matrix question still needs a
  precise surviving target and further status work. Absolute values around
  $A^{-1}$ are essential.
- **Stable selected bidiagonal singular vectors.** IE-09 is retained as an
  uncounted candidate in its chapter. A cost constant allowed arbitrary
  dependence on fixed precision, combined with $nu$ small, makes an asymptotic
  $O(nk)$ requirement vacuous. A faithful precision model is still needed.
- **Sorted compensated summation.** Higham ASNA Problem 4.10 needs an exact
  floating-point model and a quantitative error threshold before “large
  relative error” becomes a well-defined minimum-length question. No entry yet.
- **Least-squares stability.** Higham ASNA Problem 20.12 concerns
  mixed-versus-backward stability for equality-constrained LS; 20.13 concerns
  row-wise backward error for unconstrained LS.
  The perturbation model, requested computational bound, and later status
  still need checking. A generic quantifier-elimination procedure would not
  answer the intended practical question.
- **Jordan structure of bivariate matrix polynomials.** Noferini
  [§4.3, Problem 4.19](https://arxiv.org/html/2512.08399v5#S4.SS3) asks for a
  structural classification of rank drops of specified integer Toeplitz
  matrices. Ordinary finite matrix-rank computation is already available;
  an entry must make clear what additional classification is sought.
- **Fractional Helmholtz preconditioning extensions.** Adriani et al.,
  [LAA 708 (2025), 551–584](https://uu.diva-portal.org/smash/get/diva2:1925024/FULLTEXT01.pdf),
  §6, lists extensions to other discretizations and domains. These are research
  directions rather than ready-made quantified statements, so none is counted.

## Coverage still missing

The target of 1,000 requires much broader primary-source coverage. Books on
iterative methods, least squares, structured matrices, inverse problems,
matrix polynomials, and numerical tensor methods remain substantially
unscreened. Trefethen–Bau's [author page](https://people.maths.ox.ac.uk/trefethen/text.html)
was located, but locating a book or its preview is not recorded as reading its
contents. Future additions must trace an actual statement and check subsequent
work; a title does not contribute entries merely by appearing here.
