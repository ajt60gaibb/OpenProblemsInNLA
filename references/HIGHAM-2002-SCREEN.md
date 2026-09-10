# Screening the supplied Higham 2002 leads

Checked **2026-09-08** against the existing 72-entry collection, the supplied
reading notes, Higham's *Accuracy and Stability of Numerical Algorithms*,
second edition, and targeted later primary literature. This is a selected-passage
screen of the supplied leads, not a cover-to-cover certification or a proof audit.

**Three additions:** [IE-13](../linear-systems-and-elimination/IE-13/README.md),
[IE-14](../linear-systems-and-elimination/IE-14/README.md), and
[IE-15](../linear-systems-and-elimination/IE-15/README.md), bringing the collection
to **75**. Each has both editorial ratings and individual Markdown, TeX, and PDF
files. Their status evidence is limited: the source explicitly poses the questions,
and the later searches found no resolution, but no recent explicit reaffirmation
of these particular questions' openness was located.

“Uncounted” below means that a precise surviving statement or its current status
was not established; it does **not** mean that the research direction is solved.
Different algorithms and perturbation models are kept distinct. No problem was
attempted or solved during this screen.

## Numbered research problems

| Book problem | Disposition | Scope and evidence |
| --- | --- | --- |
| 4.10, p. 92: sorted compensated summation | Uncounted | “Large relative error” needs a quantitative threshold and a fixed arithmetic model before a minimum length is well-defined. Three-term accuracy and the six-term example do not supply that missing specification. |
| 5.7, p. 104: fast polynomial evaluation | Uncounted | The source concerns evaluation schemes with coefficient preprocessing. It asks for analyses and experiments, without a particular unresolved bound. Ordinary Horner, compensated Horner, and multipoint evaluation are not interchangeable substitutes. |
| 9.15(a), p. 193: unequal bandwidths | **Added IE-13** | Sharp GEPP growth as a function of lower and upper bandwidth, uniform in dimension. Includes zero-bandwidth boundary cases and complex inputs, following the adjacent definitions. |
| 9.15(b), p. 193: quasi-tridiagonal matrices | **Added IE-14** | Exact growth for the tridiagonal pattern with two nonzero corners. This is distinct from fixed bandwidth and from algorithms called cyclic reduction. |
| 9.16, p. 193: practical GEPP growth | Related entry already present; broad version uncounted | IE-04 is a separately sourced, precise smoothed-analysis conjecture. A general explanation has no prescribed input distribution or probability target. Gaussian average-case theory is substantial partial progress [1]. |
| 9.17, p. 193: complete pivoting | Part resolved; part duplicate | The current quasipolynomial lower bound implies the requested ratio to dimension tends to infinity [2]. This is an inference from the claimed theorem, not an independent proof audit. The Hadamard question is already IE-03. |
| 9.18, p. 193: rook pivoting | **Added IE-15** for the small-order part | The exact constants in orders three and four form one entry. General lower-bound requests have later answers [2,3]; those do not determine this pair. |
| 10.12, p. 212: growth below three | Resolved | The class is complex symmetric $A=B+iC$ with real symmetric positive definite $B,C$, using elimination without pivoting. Its sharp class supremum is two [4]. The supplied description as merely nonsymmetric positive definite would change the problem. |
| 11.10(a), p. 229: Bunch–Kaufman growth | Historical sharpness substantially answered; exact residual uncounted | The 2011 construction closes the exponential growth rate, with a constant-factor gap for the book's algorithm [5]. No new exact-extremum statement is admitted from that gap alone. |
| 11.10(b): symmetric rook growth | Uncounted; source conflict | The 2011 paper leaves high-growth examples for bounded pivoting outside its constructions [5]. A later survey states a different upper bound [6]; the pivot rule and primary derivation need reconciliation before retaining the old attainability question. This is not ordinary LU rook pivoting. |
| 11.10(c): skew-symmetric Bunch growth | Uncounted | The original bound and algorithm are identifiable [7], but the later sharpness status remains insufficiently established. Odd-order skew-symmetric matrices also preclude a careless nonsingularity assumption. |
| 11.10, Aasen part | Superseded | The old upper bound was improved in 2019; the replacement bound is itself unattainable in orders at least six [8]. A new exact-growth problem would need separate sourcing and screening. |
| 12.5, pp. 242–243: one refinement step | Uncounted | Fixed-precision componentwise stability needs the exact conditioning/scaling assumptions and uniform error bound. Fixed-data first-order statements are already available [9]; mixed-precision results do not settle this question. |
| 15.8, p. 304: inverse-factor overestimate | Full-matrix question uncounted; tridiagonal lead withheld | The denominator contains $|A^{-1}|y$, not $A^{-1}y$. The narrower dimension-independent tridiagonal conjecture has a 2014 published resolution claim [10]. That does not establish a solution of the book's full-matrix maximum problem. |
| 16.5, p. 319: Sylvester solution conditioning | Partial answer found; uncounted | A September 3, 2026 preprint directly addresses the question [11]. It concerns conditioning of the solution matrix itself, not of the Kronecker linear operator. The broad request supplies no particular remaining extremal bound. |
| 18.3, p. 352: scalloping in matrix powers | Uncounted | The exact-arithmetic phenomenon is identified, but a precise class, observable, and asymptotic claim are not specified. The original matrix-power paper is relevant context [12]. |
| 18.4, p. 352: Schur-based convergence condition | Uncounted | “Sharp” needs a defined comparison class and arithmetic/powering model. The existing Jordan-based and Schur-related analysis [12] cannot be repackaged as a new conjecture without specifying the surviving quantitative target. |
| 20.12, p. 406: mixed versus backward stability | Uncounted | The Gu/Stewart perturbation restrictions must first be recovered faithfully [13]. Allowing all coefficient blocks arbitrary normwise perturbations risks changing the intended question. |
| 20.13, p. 406: row-wise LS backward error | Uncounted | This is **unconstrained** least squares. A “computable expression” needs a specified effective target beyond an infimum definition or generic real-algebraic computation. Normwise formulas are not row-wise formulas. |
| 22.3(c), p. 430: Vandermonde inversion | Uncounted | The source requests forward/residual analyses for particular inverse algorithms, including the orthogonal-polynomial extension [14]. A precise surviving claimed bound was not verified. This is not the Björck–Pereyra solve algorithm. |
| 23.10, p. 449: Strassen/Winograd accuracy | Experimental direction, uncounted | Later work provides extensive analysis and direct experiments [15]. The exercise itself specifies an investigation rather than an unresolved proposition. |
| 26.2(b), p. 487: Sherman–Morrison stability | Strong candidate; still uncounted | Modern work explicitly leaves unconditional condition-number-dependent bounds open [16]. Its conditional analysis and omitted rounding operations must not be silently converted into a full-model theorem target. |
| 26.3, p. 487: cubic formulas | Uncounted | The book already shows instability, including for its sign-improved formula. Later solvers [17] change the algorithm; a source-backed unresolved quantitative bound for the textbook formulas was not established. |
| 28.2, p. 525: random orthogonal/banded matrices | Uncounted | Householder/Givens comparison and banded generation require a precise distribution or optimality/complexity question. A short random Givens product is not automatically Haar distributed [18]. |
| 26.4: direct search on other research problems | Methodological lead only | A suggested tool for investigation does not constitute an additional mathematical question. |

## Prose leads and earlier exclusions

- **Reliable condition estimation, p. 288:** uncounted pending a faithful computational
  model. Demmel–Diament–Malajovich's reduction to zero-product testing [19] does
  not by itself identify the latter's complexity with matrix multiplication.
  Deterministic and randomized guarantees, and arithmetic and bit models, must
  not be conflated.
- **Classical Gram–Schmidt orthogonality:** the historical absence of a useful
  bound is obsolete. Giraud–Langou–Rozložník–van den Eshof [20] prove a bound
  with quadratic dependence on the input condition number under numerical
  nonsingularity of the normal equations. Do not add the old claim.
- **Pseudospectra and stationary iteration:** uncounted as a broad research
  direction. Matrix-power analysis already supplies relevant partial theory [12];
  no precise surviving proposition was identified by this screen.
- **Generalized-QR backward stability for constrained LS:** overlaps the
  perturbation-model issue in 20.12. Algorithm-specific results [21] must not
  be mistaken for a general mixed-to-backward implication. No separate admission.
- **Fast Vandermonde QR error analysis:** uncounted. This names an analysis
  program without selecting a verified unresolved bound for a fixed algorithm;
  it is also distinct from inverse formation in 22.3(c).

The supplied notes already distinguish the historical Gauss–Jordan row-dominance
question and triangular prescribed-singular-value construction as solved before
the second edition. Neither is proposed for admission here. Forsythe's conjecture
remains excluded following the earlier September 2026 correction.

## Primary references and limits of access

The book was checked using its [SIAM record](https://doi.org/10.1137/1.9780898718027)
and [university-hosted PDF](https://pages.stat.wisc.edu/~bwu62/771/hingham2002.pdf).
Critical matrix patterns, absolute-value signs, and algorithm definitions were
inspected in page images. Each added entry records its own specific search terms.

1. Huang and Tikhomirov, [*Average-case analysis of the Gaussian elimination with partial pivoting*](https://doi.org/10.1007/s00440-024-01276-2), PTRF 189 (2024), 501–567.
2. Shah and Urschel, [*Entry growth in Gaussian elimination*, v4](https://arxiv.org/html/2608.19189v4), August 31, 2026, Theorems 2.2–2.3, 1.6/6.2, and 1.7/7.12. Asymptotic conclusions are manuscript claims screened for scope.
3. Edelman and Urschel, [*Some New Results on the Maximum Growth Factor in Gaussian Elimination*](https://arxiv.org/html/2303.04892v4), SIMAX 45 (2024), §6.
4. Drury, [*Fischer determinantal inequalities and Higham's Conjecture*](https://doi.org/10.1016/j.laa.2013.08.031), LAA 439 (2013), 3129–3133; Teng Zhang, [*Sharp condition-number bounds for growth factors of Higham matrices in Gaussian elimination*](https://arxiv.org/html/2604.23024v1), §1.1, Remark 1.2, Appendix A. The Drury DOI replaces an erroneous earlier link to Guo–Gu–Li's arXiv:1305.5211; Zhang is one author.
5. Druinsky and Toledo, [*The growth-factor bound for the Bunch-Kaufman factorization is tight*](https://www.cs.tau.ac.il/~stoledo/Bib/Pubs/bkbound.pdf), SIMAX 32 (2011), 928–937, Theorems 1–2 and §6. Algorithm D and the book's A/B rule have different exact sharpness conclusions.
6. Scott and Tůma, [*Direct Methods for Sparse Matrices*, Chapter 7](https://doi.org/10.1007/978-3-031-25820-6_7), 2023, §7.2.4. The symmetric-rook upper-bound attribution requires a primary-source check; it is not adopted as a resolution.
7. Bunch, [*A Note on the Stable Decomposition of Skew-Symmetric Matrices*](https://doi.org/10.1090/S0025-5718-1982-0645664-X), Math. Comp. 38 (1982), 475–479, §3.
8. Feng and Lu, [*On the growth factor upper bound for Aasen's algorithm*](https://arxiv.org/abs/1805.08994v2), Applied Mathematics Letters 88 (2019), 118–124.
9. Higham, [*Iterative Refinement for Linear Systems and LAPACK*](https://www.netlib.org/lapack/lawnspdf/lawn104.pdf), §§4–5, 7; IMA J. Numer. Anal. 17 (1997), 495–509.
10. Higham, [*Bounding the error in Gaussian elimination for tridiagonal systems*](https://eprints.maths.manchester.ac.uk/354/1/0611036.pdf), SIMAX 11 (1990), §4, p. 527; Huang, Liu, and Zhu, [*Accurate solutions of diagonally dominant tridiagonal linear systems*](https://link.springer.com/article/10.1007/s10543-014-0481-5), BIT 54 (2014), 711–727. The publisher abstract explicitly claims a resolution; the full theorem was not retrieved, so no exact constant or full-matrix extension is asserted.
11. Fasi and Hashemi, [*Conditioning of solutions to the Sylvester equation*](https://arxiv.org/html/2609.04050v1), September 3, 2026, §§4–7. Gives examples separating solution conditioning from operator conditioning and bounds for several classes; expressly a partial answer.
12. Higham and Knight, [*Matrix powers in finite precision arithmetic*](https://eprints.maths.manchester.ac.uk/345/1/0616025.pdf), SIMAX 16 (1995), 343–358, §§3–4.
13. Gu, [*Backward Perturbation Bounds for Linear Least Squares Problems*](https://doi.org/10.1137/S0895479895296446), SIMAX 20 (1998), 363–372. The complete original perturbation theorem was not recovered; its abstract and a related author report do not justify an unrestricted restatement.
14. Calvetti and Reichel, [*Fast inversion of Vandermonde-like matrices involving orthogonal polynomials*](https://doi.org/10.1007/BF01990529), BIT 33 (1993), 473–484; Skrzipek, [*Inversion of Vandermonde-Like Matrices*](https://doi.org/10.1023/B:BITN.0000039420.97768.49), BIT 44 (2004), 291–306. Later full-text access was limited; abstracts do not establish the precise error-bound status.
15. Ballard, Benson, Druinsky, Lipshitz, and Schwartz, [*Improving the Numerical Stability of Fast Matrix Multiplication*](https://arxiv.org/abs/1507.00687), SIMAX 37 (2016), 1382–1418; [*Alternative Basis matrix multiplication is fast and stable*](https://doi.org/10.1007/s00211-026-01531-9), Numerische Mathematik 158 (2026), §6.1.1 and Fig. 4.
16. Hashemi and Nakatsukasa, [*Instability of the Sherman-Morrison formula and stabilization by iterative refinement*](https://arxiv.org/abs/2510.01696), inspected PDF v1, October 2, 2025, §3, paragraph after Proposition 3.2, and §4. The HTML's displayed August 2026 date was not verified as an arXiv revision. The further [Ma et al. inverse analysis](https://arxiv.org/abs/2504.04554) uses a different arithmetic model.
17. Flocke, [Algorithm 954: *An Accurate and Efficient Cubic and Quartic Equation Solver for Physical Applications*](https://doi.org/10.1145/2699468), ACM TOMS 41 (2015), Article 30. Full article access was unavailable; an alternative solver is not a proof about the book's formulas.
18. Anderson, Olkin, and Underhill, [*Generation of random orthogonal matrices*](https://doi.org/10.1137/0908055), SIAM J. Sci. Stat. Comput. 8 (1987), 625–629.
19. Demmel, Diament, and Malajovich, [*On the Complexity of Computing Error Bounds*](https://doi.org/10.1007/s10208001004), FoCM 1 (2001), 101–125. The book and abstract identify the reduction; no full-model complexity conjecture is admitted from them alone.
20. Giraud, Langou, Rozložník, and van den Eshof, [*Rounding error analysis of the classical Gram-Schmidt orthogonalization process*](https://www.stat.uchicago.edu/~lekheng/courses/31060w14/GLRV.pdf), Numerische Mathematik 101 (2005), 87–100.
21. Cox and Higham, [*Row-wise backward stable elimination methods for the equality constrained least squares problem*](https://eprints.maths.manchester.ac.uk/353/1/33595.pdf), SIMAX 21 (1999), 313–326.

The search used exact problem numbers, named algorithms, original-paper titles,
conjecture descriptions, and 2025–2026 follow-up queries. This does not exclude
unindexed or unpublished solutions. No full resolution is inferred merely from
an abstract saying that a paper “addresses” a problem; the Sherman–Morrison
case illustrates why the actual conditional theorem matters.
