# Randomized, low-rank, and related matrix-theory candidate screen

**Final audit correction (2026-09-11):** The initial symmetric rank-two recommendation below is superseded by the [RA-20 negative resolution](ra20-resolution/README.md): its admitted n=s=3 case has ED degree three, not four. The original target and ID are retained as Solved (refuted); the other formula cases are not thereby established. The following screen is preserved as the preparation record.

Checked 2026-09-11. These research notes preceded allocation; see the
[admission record](README.md) for final IDs and decisions. Existing CATALOG.md, CONTRIBUTING.md,
SCREENED-OUT.md, and the earlier expansion/screen records were checked for
duplicates. The user named Bartlett as an example; searches involving Peter
L. Bartlett, Bartlett decompositions, least squares, and kernel matrices did
not establish a new precise source-stated NLA conjecture attributable to him.
Do not misattribute the adjacent-author candidates below to Bartlett.

## 1. Recommended: number of labeled real Hadamard matrices

Let
\[
 H(n)=\#\{H\in\{-1,1\}^{n\times n}:HH^{\mathsf T}=nI_n\}.
\]
Conjecture: an absolute constant \(C>0\) satisfies
\[
 H(n)\le 2^{C n\log_2 n}
\]
for every positive integer \(n\) divisible by four. These are actual labeled
matrices, not equivalence classes under signed row/column permutations.

Primary source: A. Ferber, V. Jain, Y. Zhao, *On the number of Hadamard matrices
via anti-concentration*, Combinatorics, Probability and Computing 31 (2022),
455–477, **Conjecture 1.3**, p.456, immediately following Theorem 1.2.
[Published full text](https://doi.org/10.1017/S0963548321000377),
[published PDF](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/887EFBBF79B804BCDD942029283D4CD7/S0963548321000377a.pdf/on_the_number_of_hadamard_matrices_via_anticoncentration.pdf),
[arXiv record](https://arxiv.org/abs/1808.07222).
The older author PDF numbers this Conjecture 1.4; use the published numbering.

Known bound: Theorem 1.2 proves
\(H(n)\le2^{(1-c_H)n^2/2}\) for an absolute \(c_H>0\) and all sufficiently
large multiples of four. Whenever one such matrix exists, its row permutations
give at least \(n!\) distinct matrices. Do **not** repeat the older manuscript's
incorrect claim that independently permuting rows and columns always produces
\((n!)^2\) distinct matrices; the published version corrects this to \(n!\).

Current-status evidence: the problem is restated as Conjecture 28 in the
[2024 BIRS report](https://www.birs.ca/workshops/2024/24w5204/report24w5204.pdf)
and discussed as conjectural in J. Peca-Medlin, *Complete pivoting growth of
butterfly matrices and butterfly Hadamard matrices* (2026), **§3 before
Proposition 3.1** ([publisher](https://doi.org/10.1080/03081087.2026.2660796)).
The latter counts particular butterfly constructions, not all Hadamard
matrices. Exact-title, author-name, `number of Hadamard matrices conjecture
2026`, and `Hadamard matrices Ferber Jain Zhao 2026 upper bound` searches found
no full upper-bound proof or counterexample.

NLA connection: counting flat orthogonal sign transforms and exact matrix
designs; the recent butterfly paper explicitly connects this enumeration to
structured orthogonal transformations and elimination. Distinct from FR-08's
existence in each order, IE-03's pivot growth for existing matrices, and TR-01's
random-embedding dimension. Suggested difficulty: extreme; importance:
interesting to the community. The known exponent is still quadratic.

## 2. Recommended: determinant product inequality for Wishart blocks

Let \(p_1,\ldots,p_d\) be positive integers, \(p=\sum_i p_i\), \(\alpha>p-1\),
and \(\Sigma\in\mathbb R^{p\times p}\) symmetric positive definite. Let
\(X\sim W_p(\alpha,\Sigma)\) have density on positive definite symmetric matrices
proportional to
\[
 (\det X)^{(\alpha-p-1)/2}
 \exp[-\tfrac12\operatorname{tr}(\Sigma^{-1}X)].
\]
Partition \(X=(X_{ij})\) into blocks of sizes \(p_i\times p_j\).
For every \(\nu_1,\ldots,\nu_d\ge0\), is
\[
 \mathbb E\prod_{i=1}^{d}(\det X_{ii})^{\nu_i}
 \ \ge\ \prod_{i=1}^{d}\mathbb E(\det X_{ii})^{\nu_i}
\]
always true? All moments displayed are finite. The block count and exponents
belong together in one entry.

Primary source: C. Genest, F. Ouimet, D. Richards, *On the Gaussian product
inequality conjecture for disjoint principal minors of Wishart random
matrices*, Electronic Journal of Probability 29 (2024), paper 166,
**Conjecture 1.1, equation (6); Definition 2.4**.
[Current full text, v3 dated 2024-10-01](https://arxiv.org/html/2311.00202v3),
[record](https://arxiv.org/abs/2311.00202),
[journal DOI](https://doi.org/10.1214/24-EJP1222).

Known cases: \(d=2\) is proved in Genest–Ouimet–Richards, *An explicit Wishart
moment formula for the product of two disjoint principal minors*, Proceedings
of the AMS 153 (2025), 1299–1311,
[full text](https://arxiv.org/html/2409.14512),
[DOI](https://doi.org/10.1090/proc/17077). The EJP paper's Remark 1.2 records
this case. Block-diagonal scale matrices give independence and equality.
Negative-exponent results from the EJP paper are a different regime.

Current-status boundaries: Gaunt–Ouimet, *On Wilks' problem: Exact recursive
formulas via Stein's method for the joint moments of disjoint principal minors
of Wishart random matrices*, July 2026,
[full text](https://arxiv.org/html/2607.03984), gives a moment recursion; it
does not state a proof of this all-real-exponent inequality. Ouimet–Greaves's
2026 manuscript [*A proof of the strong Gaussian product inequality
conjecture*](https://www.researchgate.net/profile/Frederic-Ouimet/publication/410720385_A_proof_of_the_strong_Gaussian_product_inequality_conjecture/links/6a67b848f475b23f400ec34e/A-proof-of-the-strong-Gaussian-product-inequality-conjecture.pdf),
**Theorem 2.1**, claims the scalar Gaussian-coordinate inequality. Its
introduction distinguishes the Wishart extensions; no determinant-block
theorem is asserted there. This screen checked its stated scope, not its proof.
The scalar result is not silently treated as a Wishart determinant result.

Searches: `Wishart product inequality proof 2026`, `Wishart Conjecture 1.1
2025`, `Ouimet Greaves Wishart`, exact title; current arXiv version and
[Ouimet's publication list](https://sites.google.com/site/fouimet26/research)
checked. No full resolution of the displayed target found. Suggested status:
partially resolved; difficulty: challenging; importance: interesting to
specialist. NLA connection: determinants of sample-covariance blocks are
squared volumes of Gaussian column blocks, linking this to random Gram
matrices and volume-based matrix methods. No existing entry has this target.

## 3. Candidate with explicit notation caveats: sparse permuted-matrix ESD

Primary source: J. Peca-Medlin, *Distribution of the number of pivots needed
using Gaussian elimination with partial pivoting on random matrices*,
Annals of Applied Probability 34 (2024), 2294–2325,
**§5.2, equations (28)–(30), footnote 9, Conjecture 1 on preprint p.17**.
[Current v2 PDF](https://arxiv.org/pdf/2301.13452),
[record, v2 dated 2023-09-14](https://arxiv.org/abs/2301.13452),
[DOI](https://doi.org/10.1214/23-AAP2023).

For fixed \(\alpha\in[0,1)\), define the cutoff
\[
k_{n,\alpha}=\begin{cases}
n+\tfrac12(1-\sqrt{1+8n^2\alpha}),&\alpha<1/2,\\
0,&\alpha=1/2,\\
-n+\tfrac12(-1+\sqrt{1+8n^2(1-\alpha)}),&\alpha>1/2.
\end{cases}
\]
Let \(P_n,Q_n\) be independent uniform permutation matrices. Independently
form \(L_n\) whose allowed entries are independent copies of a scalar \(\xi\)
with mean zero, variance \(\sigma^2=\mathbb E|\xi|^2>0\), and finite fourth
absolute moment. In the *numbered conjecture's* convention set
\((L_n)_{ij}=0\) when \(i+\lfloor k_{n,\alpha}\rfloor<j\), and fill the
other positions. Set \(A_n=P_nL_nQ_n/\sqrt{n\sigma^2(1-\alpha)}\).

The conjecture asserts probability measures \(\nu_\alpha\), independent of
the law of \(\xi\), supported on the closed complex unit disk, such that
\[
 \frac1n\sum_{j=1}^n\delta_{\lambda_j(A_n)}
 \ \Longrightarrow\ \nu_\alpha
\]
weakly in probability and almost surely, with total-variation limits
\(\nu_\alpha\to\operatorname{Unif}(\mathbb D)\) as \(\alpha\downarrow0\),
and \(\nu_\alpha\to\delta_0\) as \(\alpha\uparrow1\).

**Admission caveats:** the source has two literal notation discrepancies.
Equation (30) makes the zero condition `<=`, whereas Conjecture 1 prints `<`.
Conjecture 1 drops the square in its variance definition, while Theorem 3 and
the preceding discussion explicitly use \(\mathbb E|\xi|^2\). An entry must
state which boundary convention it retains and flag the variance typo;
do not silently combine formulas. The strict inequality above follows the
numbered conjecture. A change on one diagonal is not automatically harmless
for nonnormal eigenvalue measures, so equivalence is not claimed here.

Known case: \(\alpha=0\) is the circular law (source Theorem 3/Remark 7).
Right permutation is redundant by similarity (Remark 8). The numerical data
compare Gaussian, Rademacher, and real/complex uniform entries.

Status search: exact title, `Peca-Medlin Conjecture 1 sparsity`, `random
permuted triangular spectral matrix 2025 2026`, author publications.
The [current author research page](https://sites.google.com/view/john-peca-medlin/research)
still describes these as universality conjectures; later butterfly-tree and
pivot-probability papers concern other statistics. No full solution located.
No catalog duplicate: TR-07 is about random column subsets, not an empirical
eigenvalue limit. NLA connection is explicit in the source: random ensembles
with prescribed GEPP movement and sparsity. Proposed rating: challenging /
interesting to the community. Consider holding for source-convention review.

## 4. Low-rank zeros: source-stated enumerative targets, with edge cases

Primary source: K. Kubjas, L. Sodomaco, E. Tsigaridas, *Exact solutions in
low-rank approximation with zeros*, Linear Algebra and its Applications 641
(2022), 67–97.
[Current arXiv v2 PDF, dated 2022-01-29](https://arxiv.org/pdf/2010.15636),
[record](https://arxiv.org/abs/2010.15636),
[author publication page](https://www.kaiekubjas.com/publication/kubjas-2020-exact/),
[published DOI](https://doi.org/10.1016/j.laa.2022.01.021).

For a complex matrix variety \(V\) defined over the reals, use the **bilinear**
squared Frobenius distance \(d_U(X)=\sum_{ij}(x_{ij}-u_{ij})^2\), with no
complex conjugation. The Euclidean distance degree is its generic number of
complex critical points on the smooth locus of \(V\). For symmetric matrices,
the distance is the restriction of the full Frobenius distance: off-diagonal
terms have weight two, not the unweighted norm on independent coordinates.

### 4a. Corank-one matrices with one fixed zero

For each \(n\ge3\), set
\(V_n=\{X\in\mathbb C^{n\times n}:\det X=0, x_{11}=0\}\).
**Conjecture 5.1**, preprint p.19, states
\[
\operatorname{EDdegree}(V_n)=5n-7.
\]
Table 2 verifies the values for \(3\le n\le10\) using numerical solutions
and symbolic ideal-degree checks. Source does not explicitly print the
restriction \(n\ge3\), but its entire table starts there and the \(n=2\)
variety is a union of two linear spaces with degree two, whereas the formula
would give three. Explicitly exclude this already understood endpoint and
flag it, rather than treating the source as valid for every order.

### 4b. Symmetric rank-two approximation with up to four diagonal zeros

For \(s\in\{1,2,3,4\}\) and \(n\ge\max\{3,s\}\), set
\[
W_{n,s}=\{X\in\mathbb C^{n\times n}:X^{\mathsf T}=X,
 \operatorname{rank}X\le2, x_{11}=\cdots=x_{ss}=0\}.
\]
**Conjecture 5.6**, preprint p.21, states
\[
\operatorname{EDdegree}(W_{n,s})=
\begin{cases}
3(n-1)-2,&s=1,\\
9(n-2)-2,&s=2,\\
27(n-3)+4,&s=3,\\
81(n-4)+28,&s=4.
\end{cases}
\]
Keep all four values of \(s\) in one entry. Table 7 reports checks through
\(n=10\). Rank-two approximation needs \(n\ge3\); the source table includes
the trivial \(n=2\) cases but its formula for \(s=2,n=2\) is not applicable.

These two families have genuinely different approximation constraints:
corank one in arbitrary square matrices versus fixed rank two in symmetric
matrices. They could alternatively be grouped in one structured-ED-degree
entry if that better matches repository counting policy. They are distinct
from tensor critical-point counts TR-16/17/20 and from NM-03 algorithmic
complexity. NLA connection: exact algebraic complexity of structured
Frobenius low-rank approximation and enumeration of candidate global minima.
Suggested rating: challenging / interesting to specialist; status open
(finite computational checks are not general proofs).

Searches on 2026-09-11: exact paper title plus `2026`, `Kubjas Sodomaco
Conjecture 5.1`, `Kubjas Conjecture 4.4`, title plus `proof`, `Euclidean
distance degree zero pattern symmetric rank two`; current record and
[Sodomaco's publications](https://sites.google.com/view/luca-sodomaco/home/publications)
checked. No later solution located. Publisher full text fetch failed, so
the current arXiv v2 formulas rather than an independently obtained journal
PDF were checked.

## Zeros-paper targets that should not be admitted automatically

- **Conjecture 4.4**, preprint p.12: critical-point linear span equals the
  special critical space iff the structured determinantal variety is
  irreducible. It appears to need additional hypotheses. A zero pattern
  allowing only an unrestricted upper-left \(2\times2\) block inside a
  \(3\times3\) matrix makes the rank-\(2\) constraint vacuous; the variety
  is linear and irreducible with one generic closest point, while the
  special row/column-commutator equations leave a larger critical space.
  This is an audit lead, not a counted new problem.
- **Conjecture 4.15**, preprint p.16: under irreducibility, the critical points
  satisfy \(\langle X_{[m],I},C(U_{[m],I})\rangle_F=r\det U_{[m],I}\)
  iff \(S\cap([m]\times I)=\varnothing\). Here \(|I|=m\), \(C\) is the
  cofactor matrix, and the inner product is bilinear. The printed statement
  lacks an explicit generic-data quantifier; without genericity zero or
  singular data can trivially satisfy the equation. Hold pending exact
  convention review; do not invent a universal all-data claim.
- **Conjecture 5.2**, preprint p.19: its two \(s=2\) square/rectangular labels
  contradict Table 4. For \(m=n=3\), the table says 25 but the displayed
  square formula gives 29; rectangular \(3\times4\) has the reverse issue.
  Do not silently swap the labels in a new canonical conjecture.
- **Conjecture 5.4**, preprint p.21: uses both \(m\) and \(n\) for its square
  size and an unspecified constant \(c\). It overlaps the rank-two formulas;
  its constant dependence needs clarification before precise admission.

## Other exclusions checked in this search

- Nelson–Nguyen optimal sparse OSE: already screened out for the September 2,
  2026 SparseStack full claim, [2609.02978](https://arxiv.org/abs/2609.02978).
- Saunderson–Parrilo–Willsky random ellipsoid fitting threshold: full August
  2026 claims [2608.10184](https://arxiv.org/abs/2608.10184) and the broader
  fourth-moment universality [2608.27372](https://arxiv.org/abs/2608.27372).
- Yun–Sra–Jadbabaie SS–RS–GD inequalities: Peng's
  [2607.22620](https://arxiv.org/abs/2607.22620) claims SS–RS counterexamples
  arbitrarily close to identity and an affirmative RS–GD bound. Already
  recorded in LITERATURE-EXPANSION-2026-09.md.
- Deneanu–Vu normal sign-matrix probability: C. Young's July 2026
  [2607.15294](https://arxiv.org/abs/2607.15294) claims the full sharp
  exponential order. Exclude rather than citing its older appearance as open
  alongside the Hadamard-count conjecture.
- Tan–Vershynin complex Kaczmarz phase-retrieval conjecture: resolved by
  Huang–Wang [2109.11811](https://arxiv.org/abs/2109.11811).

These are bounded literature checks; absence of a located resolution is not
a proof of openness.

## 5. Recommended: sharp exponents for structured Gaussian operator norms

An additional clean target is in
[`../../matrix-inequalities-and-norms/MI-31/README.md`](../../matrix-inequalities-and-norms/MI-31/README.md).
R. Latała and M. Strzelecka, *Operator $\ell_p\to\ell_q$ norms of Gaussian
matrices*, Advances in Mathematics 501 (2026), 111097,
[DOI](https://doi.org/10.1016/j.aim.2026.111097),
[current arXiv v3](https://arxiv.org/html/2502.02186v3) dated 2026-06-09,
**Conjecture 5** explicitly proposes the dimension-capped square-root
dependence on $p^*$ and $q$ with a universal constant. The canonical-ready
draft supplies the exact quantifiers and conventions.

The same paper's Theorem 2 **solves** its historical Conjecture 1; do not add
that fixed-$p,q$ comparison as an open entry. Conjecture 5 is the sharper
surviving quantitative question. The spectral case and constant variance
profile are known; all exponent cases remain grouped. No catalog duplicate
was found (the Gaussian trace-threshold entries and tensor type-2 question
have different targets).

On 2026-09-11 searched exact title, `Latała Strzelecka Conjecture 5 Gaussian`,
`Gaussian matrices sharp p q 2026 norms conjecture`, and
`2502.02186 conjecture proof sharp dependence`; checked the arXiv record,
published article, and the authors' University of Warsaw publication pages.
No later resolution found. Suggested rating challenging/community and
status partially resolved. Prefer this clean statement over the source-typo
leads above. The paper also proposes a Rademacher analogue in Remark 10,
equation (3), but its deletion-index conventions and later spectral-case
progress have not been fully audited here; do not admit automatically.

## 6. Recommended: moment-regular independent-entry spectral norms

[`../../matrix-inequalities-and-norms/MI-32/README.md`](../../matrix-inequalities-and-norms/MI-32/README.md) gives a
fourth clean canonical draft, grouping Latała–Świątkowski's
**Conjecture 4.3** with its weighted-sign special case **Conjecture 1.2** in
*Norms of randomized circulant matrices*, EJP 27 (2022), paper 80,
[current arXiv v2](https://arxiv.org/pdf/2106.03139v2), 2022-05-27.
Despite the paper title, the conjecture concerns all independent centered
real matrices under a uniform moment-doubling assumption, not just circulants.
The draft retains the source's exact $\ln(k+1)$ moment order and common
deleted row/column index set. The 2025 weighted-sign restatement's truncated
logarithm is only a comparable normalization, not a change in target.

Latała [2405.13656v2](https://arxiv.org/html/2405.13656v2), Theorems 1.1 and
1.9, proves the zero-one weight case and bounds arbitrary weighted signs
with a triple-logarithmic loss. Meller
[2512.23673v2](https://arxiv.org/html/2512.23673v2), 2026-01-29,
introduction equation (3) and Theorem 1.1, explicitly treats Conjecture 4.3
as unproved and gives a polyloglog estimate for wider symmetric entries.
The original source's Proposition 4.4 supplies the Gaussian-mixture case.
These results establish a meaningful Partially resolved status.

Searched both exact paper titles, Rademacher spectral-norm conjecture/proof
2026, Latała–Świątkowski later results, and arXiv2405.13656 resolution;
checked current version histories and Meller's full introduction/theorems.
No full resolution was found on 2026-09-11. This entry is distinct from the
Gaussian $\ell_p\to\ell_q$ parameter-dependence conjecture: that one varies
the input/output norm exponents under a fixed Gaussian model, while this
one fixes the spectral norm and changes the distributional class.
