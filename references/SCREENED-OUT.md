# Screened-out questions and source cautions

These notes preserve consequential exclusions and unresolved source issues from
the former chapter pages. The underlying literature checks were made on
**2026-09-08**; the notes were consolidated on **2026-09-10** without a new
literature search. They are not additional catalog entries. A reported proof is
identified as a claim when its correctness was not independently checked;
withholding an imprecise formulation does not establish that its intended
research question is solved.

Canonical statements, their current status and their own dated evidence take
precedence over this historical record. See the [catalog](../CATALOG.md),
[resolved entries](../RESOLVED.md), and [source coverage](SOURCES.md). Repeated
notation, old counts, navigation stubs and superseded admission decisions have
been omitted.

<a id="screened-items-that-are-not-counted"></a>

## Embeddings, randomized algorithms and tensor computations

| Historical question | Evidence and scope |
| --- | --- |
| Optimal SparseStack oblivious subspace embedding | Diar Heidary, [*SparseStack Is an Optimal Oblivious Subspace Embedding*](https://arxiv.org/abs/2609.02978), submitted September 2, 2026, claims the Nelson–Nguyen conjecture. Admission was suspended on that claim. SparseStack uses a different distribution from the two-round rerandomized Hadamard transform in [TR-01](../randomized-and-low-rank-approximation/TR-01/README.md); this is not a resolution of TR-01. |
| Constant-sparsity SparseStack injectivity | Huang, Rudelson and Tikhomirov, [July 2026 manuscript, Corollary 1.6](https://arxiv.org/html/2607.05384v2), gives a negative answer to workshop Problem 5.5. Its distinct subsequent questions are TR-07 and TR-08. |
| Polynomial conditioning of QRCP on matrices with orthonormal rows | [*Iteris: Agentic Research Loops for Computational Mathematics*](https://arxiv.org/html/2606.02484v1), §4.3 and Appendix 7, reports counterexamples to workshop Problem 4.3, including bounded-coherence families. These are reported counterexamples, not proofs independently certified by this screen. |
| Nyström diminishing returns for SDDM/SDD inverses | Matthew J. Colbrook, [*Nyström Error Beyond M-Matrices: A Minimal Diagonally Dominant Obstruction*](https://arxiv.org/abs/2607.19282), July 2026, reports an affirmative SDDM theorem and an order-three SDD counterexample, explicitly answering workshop Problem 4.6. The two matrix classes must remain distinguished. |
| Relative-error least squares and randomized SVD from oblivious subspace injection alone | Townsend and Wang, [*Oblivious Subspace Injection Is Not Enough for Relative Error*, August 2026 v2](https://arxiv.org/html/2604.10215v2), §3.1 and §4.1, gives counterexamples to workshop Problems 5.1 and 5.2 respectively. The negated implications control relative error solely by the OSI failure parameter. |
| The Hamiltonian-derived nonlinear eigenvector identity as printed | Sra, [August 2026 manuscript, Appendix A.5](https://arxiv.org/html/2608.29595v1), identifies a same-site obstruction to workshop §6.2: products of Hermitian factors acting on the same component need not be Hermitian. The proposed linear cost in the number of components also needs an input/preprocessing model for dense pair interactions. No corrected problem was silently substituted. |
| Dimension-independent column-Nyström Frobenius-error existence guarantee | Epperly's dissertation, p.185, was not copied as an open question. Wang, Zhang and Zhang, [*Towards More Efficient SPSD Matrix Approximation and CUR Matrix Decomposition*](https://www.jmlr.org/papers/volume17/15-190/15-190.pdf), Theorem 7 and the following paragraph, p.14, recover the $\Omega(1+rn/c^2)$ squared-error ratio for $c$ selected columns and cite the original 2013 lower bound. This obstructs the stated dimension-independent guarantee. |
| RPCholesky dissertation oversampling conjectures | [Epperly's August 2026 analysis](https://arxiv.org/html/2608.20633v1), Corollary 1.3 and Theorem 1.4, supersedes dissertation Conjectures 11.1 and 11.3. The spectral-error discussion also gives a logarithmic obstruction to removing the effective-dimension logarithm. The sharper later conjecture is RA-01. |

### TR-02 — Fermionic-kernel greedy cross approximation

The [August 2026 workshop revision](https://arxiv.org/html/2602.05394v3), update
after Problem 4.2, records V. S. Pendyala's [*Local-to-Global Convergence of
Greedy Cross Approximation for Totally Positive Kernels*](https://doi.org/10.5281/zenodo.21863274)
(2026). The report attributes a full solution of the logarithmic
cutoff/accuracy rate for the continuous fermionic kernel to that manuscript.
This covers the former TR-02 target; the claimed proof itself was not
independently reviewed. Gilles's [*Convergence rates for pivoted QR and
LU*](https://arxiv.org/abs/2607.26863) is related work, not the basis of the
full-resolution classification. The workshop revision superseded searches
based only on its April version. The current disposition is in
[RESOLVED.md](../RESOLVED.md#tr-02).

### Directions without a complete quantitative target

Epperly's [dissertation](https://tropp.caltech.edu/dissertations/Epp25-Making-Most.pdf),
§§20.1–20.3, pp.299–303, discusses estimation, indefinite-Hermitian methods and
stable subspace downdating. These were withheld because the proposed entries
lacked exact error or stability targets. Relevant later papers include
Hallman's [*Two Variations on the XTrace Algorithm*](https://arxiv.org/html/2512.02316v1),
§§4 and 6, and Lazzarino, Pearce and Pritchard's [generalized Nyström error
estimators](https://arxiv.org/html/2601.11493v1). Their existence does not settle
every direction in the dissertation.

<a id="excluded-and-uncounted-leads"></a>

## Structured matrix approximation

### RE-04 — Finite-family relative error

The August 21, 2026 version of [*Query Efficient Structured Matrix
Learning*](https://arxiv.org/html/2507.19290v2) still prints the finite-family
$(1+\varepsilon)$ question in §5, but an update immediately after the abstract
reports its resolution. The authors link the [argument for the improved
factor](https://github.com/PratyushAvi/Structured-Matrix-Learning/blob/main/1%2Beps-finite-family-approximation.pdf),
which they describe as human-verified as of August 2026. The update is absent
from the standalone arXiv abstract page. This catalog checked the reported
scope, not the proof itself; the present classification is
[Solution claimed](../RESOLVED.md#re-04).

The finite-family improvement does not settle the pure-relative-error question
for a linearly parameterized, generally infinite family in
[RE-05](../randomized-and-low-rank-approximation/RE-05/README.md), or the
nonadaptive query requirement in
[RE-06](../randomized-and-low-rank-approximation/RE-06/README.md). A finite
discretization of a linear family still introduces additive error unless an
additional argument removes it.

Workshop [Problems 4.4 and 4.5](https://arxiv.org/html/2602.05394v3) also suggest
kernel selection and adaptive hierarchical partitions. The former leaves
suitable hypotheses to be found; the latter does not specify the admissible
partitions and algorithmic target. Those omissions prevented separate precise
entries; they are not claims that the research directions are resolved.

## Elimination, Krylov methods and numerical accuracy

| Historical question or reserved candidate | Evidence and admission boundary |
| --- | --- |
| Polynomial worst-case complete/rook pivoting growth | Shah and Urschel, [*Entry growth in Gaussian elimination*](https://arxiv.org/abs/2608.19189), August 2026, Theorems 1.6–1.7, claims quasipolynomial lower bounds. This excludes the old polynomial conjectures while leaving the catalog's specific structured and small-order targets distinct. |
| Power-law-spectrum CG versus randomized coordinate descent | Workshop Problem 2.4 was withheld after [*Iteris*](https://arxiv.org/html/2606.02484v1#S4.SS2), §4.2, Theorem 1 and Appendix 6, claimed a fixed-parameter phase diagram. Its rate bounds are expressly not sharp; no complete sharp-rate classification is inferred. |
| Aasen's historical $4^{n-2}$ growth sharpness | Feng and Lu, [*On the growth factor upper bound for Aasen's algorithm*](https://arxiv.org/pdf/1805.08994), Applied Mathematics Letters 88 (2019), 118–124, replaces the bound by $2^{n-1}$ and shows that it is unattainable for $n\ge6$. A new exact-growth target needs precise pivoting and breakdown conventions. |
| Stable $O(nk)$ selected bidiagonal singular vectors, reserved IE-09 | Großer–Lang, [*The bidiagonal MRRR algorithm*](https://www.netlib.org/lapack/lawnspdf/lawn166.pdf), §4; Marques–Demmel–Vasconcelos, [2018 manuscript](https://icl.utk.edu/files/publications/2018/icl-utk-1040-2018.pdf), introduction and cluster discussion; [workshop Problem 3.8](https://arxiv.org/html/2602.05394v3#S3.SS4). Allowing arbitrary dependence of the $O(nk)$ constant on fixed roundoff $u$, while restricting $nu$, bounds $n$ and makes the asymptotic cost requirement vacuous. Uniform precision dependence must be specified. A faithful selected-SVD guarantee also needs both residual equations, approximate normalization and clustered/zero singular-value conventions; the source prints only one residual equation. No precise admitted target was established. |
| Algebraic multigrid approximate inverse | [Workshop Problem 2.3](https://arxiv.org/html/2602.05394v3) gives an approximation target without fixing the hierarchy, smoother or construction algorithm. Replacing its multigrid requirement by an unrestricted inverse algorithm changes the question. |
| Condition-independent deterministic SVD complexity | Sobczyk, [Theorem 1.2 and §5, question 2](https://arxiv.org/abs/2410.21550), gives exact factorization with approximate isometries as well as a weaker backward-approximation consequence. The source's requested retained accuracy guarantee and real-arithmetic model must be fixed before removing condition-number dependence. A generic residual guarantee is not interchangeable. |

The exact n-step CG precision question was subsequently admitted as IE-20;
the former generic reserve is superseded. Broad GMRES explanations, block
rounding analyses and unspecified MRRR conditions in
[workshop §§2.5–2.6 and §3.4](https://arxiv.org/html/2602.05394v3) remain research
directions without a selected quantified target. Forsythe's retained IE-01 and
Higham's complex-symmetric growth question are recorded with their current
evidence classification in [RESOLVED.md](../RESOLVED.md). On September 11, 2026,
IE-01 was upgraded to **Lean verified** after checking the paper's Lean formalization
and public verification record; the earlier preprint-only assessment is superseded.

## Inverse spectra

| Question | Evidence and boundary |
| --- | --- |
| Order-four symmetric stochastic spectral feasibility | Benjamin James Clark's [2026 dissertation](https://rex.libraries.wsu.edu/esploro/outputs/doctoral/The-Nonnegative-Inverse-Eigenvalue-Problem-A/99901393504301842), Chapter 3, Theorem 3.0.1, claims the revised Kaddoura–Mourad criterion. For $1=\lambda_1\ge\lambda_2\ge\lambda_3\ge\lambda_4\ge-1$, it requires $\sum_i\lambda_i\ge0$ and $(1+\lambda_3)(1+\lambda_4)+(\lambda_2+\lambda_3)(\lambda_2+\lambda_4)\ge0$. The dissertation claim supersedes [Jung–Kim's 2024 description](https://doi.org/10.1515/math-2023-0176) as open; its proof was not independently verified by this screen. |
| Residual symmetric nonnegative inverse eigenvalue problem in order five | [Jin–Ke–Sui, August 2026](https://arxiv.org/html/2608.19435v1), (3)–(4) and §5, leaves $\mathcal R\setminus\mathcal W$ unclassified. The new impossible region must be removed from an older formulation. A bare request for existence of a quantifier-free criterion is already covered by real quantifier elimination; an acceptable structural classification needs a more precise output requirement. This is a formulation hold, not a resolution. |
| Uniform flat real orthogonal matrices with a prescribed constant column | [Kania, Lemma 9 and §6](https://arxiv.org/html/2509.24079v1), asks for one $\varepsilon>0$ and matrices $Q_n$ in every order, first column $\mathbf1/\sqrt n$, with $n\max_{i,\,j\ge2}|(Q_n)_{ij}|^2\le2-\varepsilon$. The older screen had not reconciled the prescribed-column constraint with subsequent flat-orthogonal constructions. Neither openness nor a resolution was certified. |
| Every normalized realizable-spectrum boundary point is radially extremal | [Johnson–Paparella, Conjecture 9.2](https://arxiv.org/html/2409.07682v2), needs a clarified ambient topology. Normalized spectra of real matrices occupy a constrained subset of $\mathbb C^n$; its ordinary ambient boundary and relative boundary are different. No replacement topology was silently chosen. |
| Totally extremal ideal Perron similarities | [Artemis–Paparella, June 2026](https://arxiv.org/abs/2606.02865), reports a resolution of the preceding character-table conjecture; the historical question was excluded on that source. |

## Matrix functions and matrix-family growth

| Question | Evidence and boundary |
| --- | --- |
| Every degree-20 polynomial using five matrix products | Jarlebring–Lorentzon, [Conjecture 11](https://arxiv.org/html/2504.01500v3), must be assessed against Sastre et al., [*Beyond Paterson–Stockmeyer*](https://wseas.com/journals/mathematics/2025/b385106-036%282025%29.pdf), §4 (2025), and its [authors' erratum notice](https://hipersc.blogs.upv.es/category/taylor-approximation/). The constructive claim and erratum prevent an unqualified reuse of the older question. No proof was certified here. |
| Sign-approximation equioscillation | [Workshop Problem 6.4](https://arxiv.org/html/2602.05394v3) leaves its $\ell^2$ approximation measure or grid unspecified. This source ambiguity prevented admission. |
| Integer-power marginal growth for arbitrary real matrix families | Jungers, §3.6, Open Questions 3–4, is superseded by Protasov–Jungers, [sublinear examples](https://arxiv.org/abs/1411.0497); Morris, [irregular growth](https://arxiv.org/abs/2111.10225); and Varney–Morris, [Corollary 6.1](https://arxiv.org/html/2209.00449), a finite family with growth comparable to $k^{1/3}$. MF-11–12 ask later questions about the remaining possibilities. |
| Conditioning versus roundoff in repeated squaring, reserved SF-02 | Higham, *Functions of Matrices*, Research Problem 10.16, p.266, and Güttel–Nakatsukasa, [2016 paper, §§4 and 4.3](https://eprints.maths.manchester.ac.uk/2322/1/paperworkingmerge.pdf), pose the nonnormal stability issue. The discarded provisional statement requested a particular polynomial factor in dimension and a linear factor in the number of squarings. Those factors were editorial inventions, not extracted source conjectures. The general direction remains uncounted. |
| Rank defects in the Toeplitz matrices of Fréchet–Jordan theory, reserved SF-03 | Noferini, [June 18, 2026 manuscript](https://arxiv.org/html/2512.08399v5), Definition 4.10 and Problem 4.19, asks which integer parameters yield deficient rank and what the defects are. Proposition 4.16 is sufficient but not necessary, as Example 4.18 shows. Computing any one finite rational matrix's rank is already possible; a nontrivial acceptable classification must be specified before admitting a generic algorithm request. This is distinct from the resolved matrix-function Jordan question in Higham Problem 3.11. |

Higham's *Functions of Matrices*, Problems 6.24 and 6.26, concern iteration
choice and direct computation of Cholesky factors. Without selected accuracy
and cost targets they remain research directions. Crouzeix's full proof claim,
the proved order-three binary finiteness subcase, and the resolution of
Higham's derivative Jordan-form question are retained in the
[source record](SOURCES.md#important-historical-questions-excluded) and
[resolved page](../RESOLVED.md).

## Positive and nonnegative factorizations

| Question | Evidence and boundary |
| --- | --- |
| Lorentz cones and the interior Ryshkov property | Oertel–Schürmann's February 2026 version asks the universal question, but [June 2026 v2, §7.3](https://arxiv.org/html/2602.05841v2), reports failure for the three-dimensional Lorentz cone. The broader geometric directions in v2 were not converted into new catalog entries. |
| Hadamard powers preserving factor width; equality of real and complex factor-width rank | Johnston–Moein–Plosker, [Question 1 and Conjecture 1](https://arxiv.org/html/2405.11556v2), LAA 716 (2025), 32–59, have claimed resolutions in Shitov's [author-posted July 10, 2026 manuscript](https://doi.org/10.13140/RG.2.2.24873.15204). Its abstract claims the power theorem and a counterexample to real/complex equality. Admission was suspended pending assessment of those proofs. |
| Maximum integer cp-rank in order two | The older question is superseded by [*11 can be reduced to 10*](https://journals.uwyo.edu/index.php/ela/article/download/9681/7201/26763) (2025), followed by Shitov's [June 13, 2026 author manuscript](https://doi.org/10.13140/RG.2.2.23558.33601), claiming sharp bound nine. The latter was not independently checked. This concerns integer factors, distinct from rational-factor existence in PF-03. |
| The unrestricted Drew–Johnson–Loewy cp-rank formula | The equality $\max_{A\in\mathcal{CP}_n}\operatorname{cpr}(A)=\lfloor n^2/4\rfloor$ for every $n\ge4$ is false: Bomze–Schachinger–Ullrich, [*From seven to eleven*](https://optimization-online.org/wp-content/uploads/2014/01/4206.pdf), LAA 459 (2014), 208–221. PF-04 retains the separate order-six question. |
| A completely positive perturbation question with inconsistent distances | Pfeffer–Samper, [§6, Problem 6.2](https://link.springer.com/article/10.1007/s00454-023-00620-y), compares distances between $A,\widetilde A$ and between $BB^\mathsf T,\widetilde B\widetilde B^\mathsf T$, while defining $B,\widetilde B$ as their factors. These are the same pair of matrices, so the printed conditions conflict for sufficiently small perturbations. A possible intended statement about factor distances or factor orbits requires clarification. |
| Description of the cp-rank-five boundary inside $\mathcal{CP}_5$ | Pfeffer–Samper, [§6, Problem 6.1](https://link.springer.com/article/10.1007/s00454-023-00620-y), suggests factor zero-pattern descriptions in §5.5. A precise deliverable beyond generic semialgebraic quantifier elimination was not fixed; no resolution is asserted. |
| General hardness of positive semidefinite rank | The generic hardness request in the 2015 survey is superseded by Shitov, [*The Complexity of Positive Semidefinite Matrix Factorization*](https://arxiv.org/abs/1606.09065), SIAM J. Optim. 27 (2017), 1898–1909, proving existential-theory-of-the-reals completeness. This does not settle every special tightness test adjacent to the historical request. |

### NM-02 — Necessity of sufficient scattering

Gillis, [*Nonnegative Matrix Factorization*](https://doi.org/10.1137/1.9781611976410),
§4.3.3.7, p.149, Definition 4.15 and Theorem 4.43, poses necessity of sufficient
scattering for uniqueness of the global minimum-volume factorization with
unrestricted-sign $W$ and column-stochastic nonnegative $H$, up to permutation.
This is not uniqueness among all factorizations or of a stationary point.
Adding $W\ge0$ changes the model and already has a counterexample in the book.

Admission was withheld because a [2021 geometric construction](https://mathoverflow.net/questions/407397/least-area-and-least-perimeter-triangles-that-contain-a-convex-planar-region-h)
claims a unique minimum-area triangle enclosing a specified quadrilateral.
Its compatibility with the source's sufficient-scattering condition after
simplex-coordinate conversion had not been checked. That lead is neither a
verified counterexample nor grounds for declaring the conjecture cleared.
The book's orthogonal-cone SSC condition must not be replaced by the stronger
dual-boundary variants distinguished in
[Gillis–Luce, §2](https://arxiv.org/html/2402.06019v1). The
[Vu Thanh–Gillis 2026 result, §II.C](https://arxiv.org/html/2602.04795v2),
is sufficient identifiability in another model, not this converse. The related
source formulation also appears in Fu et al., [Definition 3, §V.B and §VIII's
last question, p.17](https://arxiv.org/abs/1803.01257v4).

For broader fixed-rank NMF (Gillis §6.1.4, pp.199–200), hardness when rank is part
of the input does not prove hardness for each fixed rank. NM-03 records the
specifically sourced rank-two target. The book's broad noise-robustness
direction has substantial later answers in
[Barbarino–Gillis–Saha (2025), Theorems 1–2](https://arxiv.org/html/2511.04291v1);
it must not be copied as wholly unanswered. Normalized maximum-volume
identifiability in [Vu Thanh–Gillis, §§IV and VI](https://arxiv.org/html/2602.04795v2)
still needed complete proposed assumptions before a separate entry could be
formulated.

## Algebraic complexity

- Bläser's Research Problem 5.7, direct-sum additivity of tensor rank, is
  refuted by [Shitov's counterexample](https://arxiv.org/abs/1712.08660).
  It is different from the surviving asymptotic-rank conjecture AC-05.
- Bläser's Problem 5.11, unrestricted complexity of tensor rank over a field,
  has a later classification by Schaefer–Štefankovič,
  [*The Complexity of Tensor Rank*](https://arxiv.org/abs/1612.04338).
  Remaining decidability issues over $\mathbb Q$ require a separate source-faithful
  target; the older request cannot be counted unchanged.
- A bound strictly below four for the small Coppersmith–Winograd tensor is
  already available from Alman–Li; the sharper target and its primary references
  are preserved in [AC-04](../arithmetic-and-complexity/AC-04/README.md).

## Absolute value equations

- Hladík's [*Overconstrained and underconstrained systems of absolute value
  equations*](https://doi.org/10.1137/25M1744563), SIMAX 47 (2026), 244–264,
  advertises open problems in its [author abstract](https://kam.mff.cuni.cz/~hladik/publ/b2hd-Hla2026a.html).
  The full statement text was inaccessible in the September 8 screen; no
  problems were reconstructed from the abstract.
- Older uniqueness and nonnegativity questions in Hladík's
  [2023 paper, §3](https://arxiv.org/html/2209.06457v1), were withheld after
  Yadav–Dubey, [*On the properties of solution set of absolute value
  equations*](https://doi.org/10.1007/s11590-025-02255-9), Optimization Letters 20
  (2026), 611–623, online October 27, 2025, reported addressing them. Only the
  latter abstract was accessible, so exact resolution scope was not certified.
- The survey's connectedness-complexity question needs a precise complexity
  target: finite orthant decomposition already gives a decision procedure, so
  merely requesting a characterization is insufficient.
- The [2024 erratum](https://doi.org/10.1137/24M1635715) to Hladík's 2023 paper
  corrects a spectral-radius hypothesis in Proposition 3.5. That proposition
  is not used in the admitted AV-01–03 statements.
