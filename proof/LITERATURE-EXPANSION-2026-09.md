# Further literature expansion — 2026-09-08

This batch adds **12 distinct entries** to the starting 147, giving **159 / 1,000**.
Three parallel literature searches covered iterative methods and linear systems,
matrix functions and equations, and randomized/tensor methods; the root search
covered spectral perturbation, matrix nearness, and structured conditioning.
The current catalog and earlier exclusion records were used for duplication checks.
No solutions or proof attempts were made. This is selected-source coverage,
not a claim to have read every cited book or every later citation.

Each admitted entry contains its complete mathematical statement, both editorial
ratings, primary references, dated status evidence, and Markdown/TeX/PDF versions.
Related parameter regimes and supporting analytic conjectures are grouped.
No resolution was located for the admitted statements in the bounded searches;
this does not certify their current openness.

## Admitted statements and exact sources

| Entry | Primary passage | Scope retained and later check |
| --- | --- | --- |
| [IE-21](../linear-systems-and-elimination/IE-21/README.md): spherical-row deletion limit | Steinerberger, *Quantile-based Random Kaczmarz for corrupted linear systems of equations*, [Information and Inference 12 (2023)](https://doi.org/10.1093/imaiai/iaab029), §2.3, equation (8), followed by the request for a proof and quantitative bounds; [preprint](https://arxiv.org/abs/2107.05554), equation $(\diamond)$. | Worst retained smallest singular value, divided by the original operator norm, with both dimension and aspect ratio tending to infinity. Convergence in probability and flooring the row count are explicit editorial formalizations. Quantitative refinements are grouped here. |
| [IE-22](../linear-systems-and-elimination/IE-22/README.md): universal row-deletion constant | Same source, third question immediately after equation (8). | Supremum over all unit-row matrices, with uniform asymptotic quantifiers and sharpness. Distinct from IE-21's prescribed random ensemble. [Battaglia et al. 2608.27968v1](https://arxiv.org/abs/2608.27968), §1.1, still describes the random-matrix estimate as a heuristic; streaming guarantees do not settle either static target. |
| [IE-23](../linear-systems-and-elimination/IE-23/README.md): induced-norm inverse uniqueness | Dokmanić–Gribonval, [*Beyond Moore–Penrose Part I*](https://arxiv.org/abs/1706.08349), v2, §4.4, Corollary 4.2(3), Remark 4.1, p. 18. | All complex full-row-rank matrices, direct right-inverse objective, $2<p<\infty$. The companion Part II proves different, entrywise-norm generic uniqueness statements. No later induced-norm resolution found. |
| [SP-07](../eigenvalues-and-inverse-problems/SP-07/README.md): sharp normal spectral-matching constant | Bhatia, [*Perturbation Bounds for Matrix Eigenvalues*](https://epubs.siam.org/doi/10.1137/1.9780898719079.ch9), Chapter IX; pp. 154–155 independently corroborated by [Zhan's primary survey](https://math.ecnu.edu.cn/~zhan/papers/ZhanICCM.pdf), §21, Problem 27, pp. 12–13. Also [Šemrl's ICTP notes](https://indico.ictp.it/event/a08167/session/73/contribution/52/material/0/0.pdf), p. 10, Theorem 5 and following question. | All dimensions, spectral norm, matching with multiplicity. Holbrook refuted constant one. [Parusiński–Rainer 2603.23056v1](https://arxiv.org/abs/2603.23056), Proposition 3.4, still states a classical bound with $1<C<3$, but does not explicitly reaffirm unknown optimality. The explicit openness sources are historical. |
| [SP-08](../eigenvalues-and-inverse-problems/SP-08/README.md): rank-two spread maximizer | Fallat–Xing, [LMA 60 (2012)](https://doi.org/10.1080/03081087.2012.703189), §2; current explicit restatement in [Calkin et al. 2510.15919v1](https://arxiv.org/abs/2510.15919), §1. | Existence of a rank-exactly-two endpoint matrix maximizing spread over symmetric interval matrices. All intervals/dimensions grouped. The 2025 paper proves small-dimensional and selected interval cases and records a gap in its attempted general proof. Publisher confirms YongJun Xing's authorship. |
| [SP-09](../eigenvalues-and-inverse-problems/SP-09/README.md): finite block repetition and orbit distance | Marcoux–Zhang, [JFA 280 (2021), 108778](https://doi.org/10.1016/j.jfa.2020.108778), §5, Question 5.4, pp. 26–27; [institutional full text](https://uwspace.uwaterloo.ca/items/5359b050-4379-49b2-bdda-66ac3611d3ca). | Finite copies of normal matrices in the spectral norm. The direct follow-up [2508.13834v1](https://arxiv.org/html/2508.13834v1), §3.5, repeats the order-two result; Propositions 3.15/3.21 concern zero distance, while Proposition 4.14's counterexamples have no normality assumption. None settles this all-distance normal-matrix statement. |
| [MF-18](../matrix-functions-and-stability/MF-18/README.md): limiting Green-function imaginary-part rank | Guo–Kuo–Lin, [JCAM 236 (2012), 4166–4180](https://doi.org/10.1016/j.cam.2012.05.012), equation (1), Theorems 3 and 5, conjecture immediately following Theorem 5 on p. 4172; [author manuscript](https://uregina.ca/~chguo/JCAM_GuoKuoLin.pdf), pp. 1, 5–8. | Complex coefficients, specified regularization and selected stabilizing branch, finite nonsingular limit, regular polynomial and algebraically simple unit-circle eigenvalues. The source proves an upper rank bound. Its earlier SIMAX paper answers the real-coefficient special case, not this one. Guo's publication list through 2026 and targeted searches produced no general resolution. |
| [RA-12](../randomized-and-low-rank-approximation/RA-12/README.md): relative Gaussian trace threshold | Hallman, [2411.15454v1](https://arxiv.org/html/2411.15454v1#S5), §5, Theorem 6 and Conjecture 3. | Positive semidefinite matrices, effective rank, both comparison inequalities, gamma shape/rate convention, inclusive tolerance endpoint. Supporting gamma conjectures are grouped, not counted again. |
| [RA-13](../randomized-and-low-rank-approximation/RA-13/README.md): absolute Gaussian trace threshold | Same source, Theorem 7 and Conjecture 4. | Indefinite matrices, stable rank, absolute error, both inequalities and factor two. The gamma mean is $\phi^2/\lambda$. The displayed threshold tends to zero, contrary to a following prose sentence; retain the numbered formula. Hallman's [later XTrace paper](https://arxiv.org/abs/2512.02316) concerns different estimators. |
| [RA-14](../randomized-and-low-rank-approximation/RA-14/README.md): growing-rank spectral query complexity | Bakshi–Narayanan, [2304.03191v1](https://arxiv.org/html/2304.03191v1#S1.SS2), Open Question 1.10. | Simultaneous rank, dimension and accuracy dependence, all adaptive algorithms. Square-matrix formulation with an explicitly editorial two-sided oracle; source introduction describes $Av$, while Algorithm 7.4 uses $A$ and $A^T$. No equivalence between nonsymmetric one-sided and two-sided models is asserted. |
| [RA-15](../randomized-and-low-rank-approximation/RA-15/README.md): Schatten-to-spectral query transition | Same source, Open Question 1.11. | Rank one with varying Schatten exponent; same transparent oracle convention. Distinct from RA-14 despite a shared endpoint. Include finite-dimensional saturation. [Kacham–Woodruff 2024](https://arxiv.org/abs/2407.11959) improves running times; [Chen et al. 2025](https://arxiv.org/abs/2508.06486) studies block sizes. Neither supplies the joint characterization. |
| [TR-20](../tensor-computations/TR-20/README.md): rank-one Rayleigh–Ritz discriminant degrees | Borovik–Friedman–Hoşten–Pfeffer, [2512.06939v2](https://arxiv.org/html/2512.06939v2), §3.2, Proposition 3.7, definition before Example 3.11, Conjecture 3.18; §7.2, Table 4. | Nonisotropic degeneracy locus, complex bilinear transpose, reduced projective degree. Both source formulas are one entry. June 2026 v2 retains the conjecture. Generic critical-point counts, including existing TR-16/17, are different invariants. |

## Important rejected questions and reserves

These are uncounted. A claimed resolution is screened for scope, not independently
verified as a proof. Inaccessible or ambiguous sources remain holds rather than
assertions that a conjecture has been solved.

| Candidate | Source or later evidence | Disposition |
| --- | --- | --- |
| Square full-rank Kaczmarz–Kac convergence and rate | [Steinerberger 2411.06614](https://arxiv.org/abs/2411.06614); [Detherage–Shah 2411.16101v3](https://arxiv.org/abs/2411.16101), §2; [2505.02023v4](https://arxiv.org/html/2505.02023v4), Remark 6 and Corollary 4.4. | Later results prove the independent-vector/positive-definite Gram case. Exclude the historical target. |
| One-extra-row Kaczmarz–Kac limiting spectrum | Steinerberger, 2411.06614v1, §1.4, Figure 6; [author's open-problem list](https://faculty.washington.edu/steinerb/openproblems.pdf), Problem 56, pp. 54–55, corroborated through indexed primary text. | Reserve. The source predicts singular values $\sqrt2,1,\ldots,1$ experimentally. Universal almost-sure convergence for every initial matrix is not explicitly stated and would be a substantive strengthening. Do not manufacture its stochastic quantifiers. |
| SS–RS–GD conjecture, including matrices near identity | Yun–Sra–Jadbabaie, [COLT 2021](https://proceedings.mlr.press/v134/yun21a/yun21a.pdf), Conjecture 1; [Peng 2607.22620](https://arxiv.org/abs/2607.22620). | Current primary abstract claims SS–RS counterexamples arbitrarily close to identity and an affirmative RS–GD result. Withhold under that resolution claim. |
| Guo's reducible singular M-matrix Riccati conjecture | Guo, [1212.6461](https://arxiv.org/abs/1212.6461), Conjecture 12; Guo–Lu, [1503.07226](https://arxiv.org/abs/1503.07226), Theorem 2, published [LAA 493 (2016)](https://doi.org/10.1016/j.laa.2015.11.024). | Resolved by the later theorem. |
| Condition-independent Lanczos near-instance-optimality for Stieltjes functions | Schweitzer, [2503.04427](https://arxiv.org/abs/2503.04427); Chen–Persson, [2608.07160](https://arxiv.org/abs/2608.07160). | The August 2026 source claims matching optimality for a condition-dependent factor. Do not promote an older uniform constant-factor suggestion. |
| Matrix-polynomial bundle closures beyond grade one | De Terán–Dopico–Koval–Pagacz, [2402.16702](https://arxiv.org/abs/2402.16702). | The paper itself resolves the historical problem. Its broad structured extensions were not converted into invented precise conjectures. |
| Extended-Krylov Lyapunov prefactor | Knizhnerman–Simoncini, [Numerische Mathematik 118 (2011)](https://doi.org/10.1007/s00211-011-0366-3), [author manuscript](https://www.dm.unibo.it/~simoncin/conv_eksmlyap6.pdf), Conjecture 3.4. | Reserve. The allowed dependence of the implicit constant is unspecified. A bound permitting arbitrary dependence on a fixed finite matrix becomes uninformative after finite exact termination; a uniform family must be justified from the source. |
| Four-factor Recht–Ré AGM | Lai–Lim, ICML 2020, §6; [2026 release and manuscript claim](https://www.evidencepress.org/releases/exact-low-length-recht-re-inequalities/). | Hold for verification of a standing unrefereed full-case claim. The underlying manuscript was not retrieved; the release alone is not an audited proof. |
| Yuan–Zontini preconditioned Gauss–Seidel comparisons | [AMC 219 (2012)](https://doi.org/10.1016/j.amc.2012.08.037), Conjectures 6.1–6.2; a 2019 Edalatpanah–Najafi proof paper was located bibliographically. | Hold. Exact primary formulas and scope of the later proof were not recovered; do not claim both are solved. |
| CG/LSQR variants of SPIR; NIPALS mixed stability; classical CGLS stability | [Epperly–Meier–Nakatsukasa 2406.03468](https://arxiv.org/abs/2406.03468); [Björck 2014](https://doi.org/10.1137/120895639); [Björck–Elfving–Strakoš](https://doi.org/10.1137/S089547989631202X). | Reserve for exact algorithm, rounding-model and perturbation quantifiers. Do not duplicate IE-20 with an unspecified solver variation. |
| Intermediate-regularity Toeplitz conditioning | [Bogoya et al. 2608.24151](https://arxiv.org/abs/2608.24151), §6. | Broad regularity, low-rank perturbation and graded-mesh directions lack a fully stated new bound and completion criterion. |
| Condition-independent deterministic SVD complexity | [Sobczyk 2410.21550v2](https://arxiv.org/abs/2410.21550), Theorem 1.2 and §5. | Reserve until the exact factorization/near-isometry accuracy and real-arithmetic model are preserved. Replacing them by a generic residual bound would change the source target. |
| General GLT geometric/Karcher means | [2505.03256](https://arxiv.org/abs/2505.03256); [2511.06312](https://arxiv.org/abs/2511.06312). | Recent resolutions and noncommuting/degenerate-symbol scope issues require a precise surviving formulation. |
| Rational-normal-curve discriminant split | [2512.06939v2](https://arxiv.org/html/2512.06939v2), Conjecture 3.14. | Explicit reserve: nonisotropic degree $6(d-1)$ and isotropic degree $2d$. Total degree is already known. TR-20 was prioritized for its direct rank-one matrix connection. |
| Tensor rank increment and fibre-cross conjectures | Tyrtyshnikov, [RNAM 35 (2020)](https://doi.org/10.1515/rnam-2020-0020); original fibre-cross interpolation literature. | Hold for primary full statements, field/model conventions, and current status. Later talk abstracts are insufficient. |
| Normal-matrix path-length constant | Bhatia, [*Spectral Variation, Normal Matrices, and Finsler Geometry*](https://doi.org/10.1007/BF02985689), [author preprint](https://www.isid.ac.in/~statmath/eprints/2007/isid200703.pdf), p. 10. | Uncounted reserve: boundedness of the dimension-dependent normal-path length constants. Preserve the path regularity convention and obtain a stronger later-status check before admission. |

Other general matrix-function stopping, preconditioning, memory and AAA stability
directions were screened in [Güttel–Kressner–Lund](https://arxiv.org/abs/2002.01682)
and [Nakatsukasa–Trefethen](https://arxiv.org/abs/2510.16237), without finding a
complete quantified target ready for admission. Recursive geometric-mean symmetry
in [Poloni](https://arxiv.org/abs/0906.3132), Conjecture 1, needs precise allowed
composition rules. Earlier excluded or admitted Forsythe, GMRES, smoothed ALS,
tensor eigenvalue multiplicity, and generic sparse pseudoinverse questions were
not counted again.

## Admission audit

Root source review checked each statement. Independent audits checked the spectral
triplet, both Hallman comparison chains, the two low-rank oracle formulations,
and the rejected Kaczmarz–Kac formalization. Key distinctions are random versus
universal extrema, relative versus absolute error, finite versus infinite block
repetition, zero versus positive orbit distance, and generic critical-point count
versus discriminant degree. The mathematical field, all quantifiers, norm
conventions, limit assumptions, and known special cases are explicit locally.

Version histories were checked as well as current accessible full text. Some
arXiv HTML header dates differ from the abstract's numbered version history;
the entries cite the actual version identifiers. Exact titles, authors, named
conjectures, and relevant 2025/2026 follow-ups were searched. Historical-status
limitations are preserved rather than upgraded to claims of proven openness.

The 12 new documents each occupy one page. All pages were visually inspected;
compilation reported no remaining overflow or missing-character warnings.
The resulting collection has 159 PDFs and 164 pages.
