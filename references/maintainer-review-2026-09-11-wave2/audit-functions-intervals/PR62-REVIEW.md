# Independent mathematical audit of PR #62

Reviewed head: `00d36f06b2698aada513f8b56940569a059d28d6` in `ajt60gaibb/OpenProblemsInNLA`.
Audit date: 2026-09-11. Frozen source: `../pr-62/`.

**Disposition: no blocking mathematical error found; acceptable with the current scope language.** The seven canonical targets AV-01, AV-02, IV-02, IV-03, IV-04, IV-05 and IV-06 are resolved in the stated sense. AV-02, IV-02 and IV-04 are complexity classifications; they do not establish P unequal to NP. This audit independently checks the arguments and exact calculations; it is not proof-assistant certification, human peer review or novelty certification.

For each of the seven entries, the entire original page from `## Problem statement` onward, including any later `Question` section, is byte-identical to published `origin/main`. IDs, canonical paths and mathematical targets are preserved. Evidence is in `independent-check-results.json`.

## AV-01 — polynomial recognition of exactly 2^n solutions

Source: `references/colbrook-intervals-2026-09-11/manuscripts/AV-01.tex`, Theorem 1 and Sections 2–4.

In each closed orthant, solutions are the intersection of an affine subspace with that orthant, hence convex. If the whole solution set is finite, there is at most one solution per orthant. Exactly 2^n distinct solutions force every orthant to have one and every solution to belong to just one orthant; thus no solution has a zero coordinate. Every sign matrix is then nonsingular: a nonzero null direction would yield a line segment remaining in the open orthant.

With `N_s=I+A D_s` and positive `u_s`, Cramer's rule gives `r_i(s)=q(s)(u_s)_i`. The numerator r_i does not depend on s_i. Adjacent cube vertices therefore have determinants of the same nonzero sign. All vertices have that same sign and their average is `q(0)=1`, so they are positive. The multiaffine interpolation weights are nonnegative and sum to one even on the boundary, making q and every r_i positive throughout the closed cube. In particular b>0. This avoids silently assuming the usual spectral-radius sufficient condition.

For any feasible y of `P={(A±I)y<=b}`, set u=b−Ay>=|y| and define d_i=y_i/u_i where u_i>0, otherwise zero. The zero-slack case is handled correctly: it first forces y_i=0, then invertibility and positivity of `(I+A D_d)^−1 b` exclude zero slack. Consequently P is exactly the continuous image `D_d u(d)` of the compact cube and is bounded with all u_i>0.

Conversely, b>0 makes P nonempty and full-dimensional. Positive slacks forbid simultaneous activity of both inequalities in a pair. Each vertex therefore has exactly one independent active normal per pair and represents a solution in an open orthant. Removing one active inequality defines a feasible ray retaining n−1 independent equalities; boundedness forces an endpoint. Only the opposite member of the removed pair can newly bind, because all other pairs retain their original active equality and cannot have both active. Its normal is independent, since it changes along the ray. This establishes closure of vertex signs under each coordinate flip and hence a vertex in every orthant. All corresponding systems are nonsingular, so there are precisely 2^n solutions and no additional boundary or continuum solutions.

The proposed recession feasibility normalization is exact: a nonzero recession vector has `−A r>=|r|` and positive `−1^T A r`, hence can be scaled to make it one. On P, u_i>=0, so testing the equality u_i=0 suffices to test failure of strict positivity. There are exactly n+1 rational LP feasibility problems, with polynomial coefficient bit lengths. Rational LP feasibility is polynomial-time; the accompanying floating point routine is correctly described as diagnostic.

The fresh exact four-solution example matches all four orthants while `rho(|A|)=6/5`. Full exact Fourier–Motzkin small-instance tests, after source audit, passed on 1,046 rational instances (dimensions 1–3), including singular matrices, nonpositive b and boundary cases. Fourier–Motzkin is used only as a checker; the theorem does not claim that elimination is polynomial-time.

**Pass: solved, including negative instances with infinitely many solutions.**

## AV-02 — spectral inverse-norm threshold hardness

Source: `manuscripts/AV-02.tex`, Lemma 1, Theorem 2 and Sections 2–3.

For a single diagonal parameter, Sherman–Morrison expresses the inverse as an affine function of `t/(1−alpha t)`. Regularity means its denominator never vanishes on the closed interval. The derivative is positive, so every interior inverse is a convex combination of the endpoint inverses. Norm convexity and successive coordinate moves put a maximum at a sign vertex; convexity of the original parameterization is not presumed.

The reduction builds upper-triangular integer A with diagonal 2, making all diagonal perturbations automatically nonsingular. I checked the block inverse: its upper-right block is `K^2 a 1^T X B Y`. The maximal norm of `x^T B` for `x in [1/3,1]^v` is `(2/3)sqrt(C)`, since the squared norm is a sum of edge differences squared and a box-vertex maximum counts crossing edges. Setting a=1 and Y=I attains this block norm; any other allowed a,Y can only reduce it. The whole inverse dominates its subblock in spectral norm, and subtracting that block leaves norm at most `1+K sqrt(v)+K sqrt(2m)<=36N^3` with K=12N^2. Therefore the two asserted bounds with main coefficient 96N^4 are valid.

For `q=floor(sqrt(144N^2 k))`, `t=8N^3 q`, a yes cut of size >=k puts the lower bound at or above t. For a no instance, the gap `sqrt(k)−sqrt(k−1)>=1/(2N)` and the floor error <1 leave >40N^3, exceeding the entire 36N^3 remainder. This is a strict no-case separation, including perfect-square floor cases. All coefficients and the threshold have polynomial magnitude in N. The unweighted MAX-CUT input used is NP-hard; the cited stronger restricted-graph result is confirmed by the [primary research manuscript](https://arxiv.org/abs/2202.13955).

For NP membership on the triangular diagonal-2 class, guessing a sign vector suffices. The equivalence `||M^−1||_2>=t iff t^2 M^T M−I is not positive definite` is exact, since it tests the smallest singular value. Exact rational Sylvester/LDL checks correctly include equality and avoid approximate singular values. This does not purport to recognize arbitrary regularity promises.

The full submitted exact suite passed for 160 graphs, 1,070 integer threshold tests and 14 explicit block inverses/NP certificates. Fresh independent integer calculations checked 4,949 gap pairs for N<=100, including threshold equality boundaries.

**Pass: solved as a many-one NP-hardness classification**, with NP-completeness proved for the stated automatically regular subclass.

## IV-02 and IV-04 — tridiagonal determinant/hull complexity

Source: `manuscripts/IV-02_IV-04.tex`, Theorems 1–2 and Section 5.

The product `M(−s/c,−1/c) M(s,−c)` is exactly the rational rotation `[[c,−s],[s,c]]` when c^2+s^2=1. The gate product `M(0,−1)M(0,q)` is `diag(1,−q)`. The continuant recursion for a tridiagonal matrix with unit superdiagonal therefore realizes the displayed product; beta_1 is correctly unused because the initial second coordinate is zero. Each q_i occurs in one distinct subdiagonal entry. No repeated uncertain parameter or dependent interval choice is hidden in the reduction.

At sign endpoints the angle recursion gives all signed sums with final sign +1: `epsilon_i=sigma_i sigma_(i+1)` recovers every desired pattern. Global sign reversal means fixing the last sign loses no partition. With delta=1/(10W^2), the cubic arctangent error is at most `delta/(150W)<=delta/10`; the total angle is <=1/(5W)<=1/5. All vertex determinants are therefore positive. Multiaffinity in the independent matrix entries makes every interior determinant a convex combination of vertex determinants, proving regularity of the *whole* interval family.

A zero integer signed sum gives determinant at least `1−delta^2/200`; no zero sum forces angle magnitude >=19delta/10 and determinant at most `1−(361/300)delta^2`. The rational threshold `1−delta^2/2` lies strictly between. Dimension is 4m−2>=2 and coefficient encoding is O(log W) per entry, so the binary reduction is polynomial even when W is numerically large. This is ordinary NP-hardness from PARTITION, not an unsupported strong NP-hardness claim.

The maximum determinant decision problem lies in NP because multiaffinity supplies an endpoint certificate and exact rational determinant computation is polynomial. For IV-04, deleting row N and column 1 leaves a triangular cofactor matrix with all diagonal entries one. Since N is even, with b=−e_N the first coordinate is `1/det T`; positivity makes its lower hull endpoint the reciprocal of the maximal determinant. Thus hardness already holds for regular matrices and a point right-hand side.

I also checked the converse complexity completion. Determinant extrema become bounded integers after a common denominator is cleared and can be found by polynomially many NP threshold queries. For general united solution sets, rowwise independent evaluation gives the stated union of 2^n rational polyhedra indexed by signs. Each lies in an orthant and is pointed. Feasible nonempty pointed polyhedra have vertices; finite coordinate optima occur at vertices. Cramer's rule gives a uniform polynomial-bit numerator and denominator bound. Feasibility and coordinate-unboundedness admit polynomial-bit sign/vertex/ray certificates. For finite endpoints, polynomially many threshold queries isolate the value in width <1/(2Q^2), and rational reconstruction uniquely recovers it. Finite unions ensure that unboundedness occurs in some member. Empty sets and infinite endpoints are explicitly covered.

Accordingly each complete exact-output polynomial-time existence question is equivalent to P=NP, not unconditionally answered by “no.” Both catalog notices state this correctly. Full exact tests passed for 430 PARTITION instances and 15,303 gate vertices; 15 checks also rebuilt the full tridiagonal matrix and exact inverse cofactor.

**Pass: IV-02 and IV-04 solved as complexity classifications.**

## IV-03 — n^2-vertex inverse-M characterization

Source: `manuscripts/IV-03.tex`, Theorem 1 and Lemmas 2–3.

The basic principal-submatrix and Schur-complement claims follow from nonsingular M-matrix closure: scaling by B^−1 1>0 makes B strictly row diagonally dominant, giving positive principal determinants and nonnegative principal inverses. Jacobi's complementary-minor identity and block inversion then transfer the stated properties to inverse-M matrices. Reducibility and zeros do not invalidate the argument.

The adjugate-completion lemma is essential and valid. If det A=0, positive (n−1)-order principal minors force rank n−1. Its rank-one adjugate has positive diagonal, so the product H12 H23 H31 equals H11 H22 H33>0, contradicting the three off-diagonal entries being nonpositive. If det A<0, B=A^−1 has negative diagonal and nonnegative off-diagonal entries; all its nonempty principal minors are negative by Jacobi. Any 3x3 principal block then has off-diagonal pair products larger than the corresponding positive diagonal products. Its determinant is `−abc+a su+b qt+c pr+p st+q ru>2abc>0`, contradiction. The proof correctly requires n>=3 and treats n=1,2 separately.

The vertex hypotheses make every lower entry nonnegative. For n=2 the single lower-diagonal/upper-off-diagonal tested vertex bounds every determinant below by a positive value. For n>=3 each proper principal interval inherits the vertex hypotheses, and induction makes every proper principal member inverse-M. For fixed distinct i,j and complement S, this gives `u=A_iS A_SS^−1>=0` and `v=A_SS^−1 A_Sj>=0` through block inversion and positive scalar Schur complements.

The derivative signs of `f_ij=a_ij−A_iS A_SS^−1 A_Sj` are then valid throughout the interval, so its minimum occurs at the entries used by V_ij. The tested vertex's two-index Schur complement is nonnegative, giving f_ij>=0 throughout the box. The identity `(adj A)_ij=−det(A_SS) f_ij` is valid even if the full matrix is singular; it follows from block elimination using only invertibility of A_SS. The completion lemma now gives det A>0, and the inverse has nonpositive off-diagonal entries. This avoids assuming the very full-matrix regularity being proved.

The n^2 tests imply the original 2n^2 equivalence because they are a subset of that two-sign family; the forward direction is immediate. Checking n^2 rational inverse-M vertices is polynomial in bit complexity, and O(n^5) counts ordinary arithmetic operations, not a strong bit-complexity bound.

The full exact suite checked 1,356 rational boxes, including all 1,296 2x2 endpoint boxes over {0,1,2}. Fresh symbolic checks verified every generic 3x3 off-diagonal adjugate identity. Finite tests supplement the general inductive proof.

**Pass: solved**, covering singularity risks, n=1,2, zero widths, zero entries and reducibility.

## IV-05 — inverse-M interval solution hull by 2n LPs

Source: `manuscripts/IV-05.tex`, Lemmas 1–2 and Theorem 3.

The secant identity for `H_sigma(x)=Cx−D_sigma R|x|` uses scalar absolute-value divided differences d_i in [−1,1]. Every secant matrix lies in the regular interval, giving injectivity. Compact regularity gives a uniform lower singular-value bound and coercivity of the squared residual. At a putative nonzero residual minimizer, no convex combination of the adjacent gradients can vanish, because it equals an invertible interval matrix transpose applied to a nonzero residual. The nearest-point projection to their compact convex hull gives one direction of strict descent for every adjacent linear piece. A sufficiently short segment remains in one such piece, contradicting minimality. Thus the elementary surjectivity proof is complete even at orthant boundaries.

For the proposed LP, P,Q are inverse-M and X=Q^−1,Y=P^−1 have positive diagonal and nonpositive off-diagonal entries. An AVE root supplies feasibility. Conversely Xy>=0 implies `y=Qv>=0`; objective sublevel sets are therefore bounded and closed, so an optimum exists. If u_k and v_k were both positive, decreasing y_k slightly would preserve their positivity and increase all other components through the nonpositive off-diagonal inverse coefficients, while strictly improving the objective. This proves complementarity at every optimum. Then x=u−v solves the original absolute-value equation exactly. The inverse-M signs, not general regularity alone, make this LP step work.

For each hull direction, rowwise interval evaluation gives the asserted signed residual inequality. In the secant comparison, row i of `M^−1 D_sigma` is nonnegative for the upper choice and nonpositive for the lower choice, yielding the corresponding bound. Taking a sign selection consistent with the optimizing root constructs an admissible matrix attaining it and the corresponding endpoint right-hand side. Thus each endpoint is an actual attainable extremum, not just an enclosure.

The 2n LPs have rational coefficients of polynomial bit length after exact inversion. No promise recognizer or general AV-03 solver is needed. Arbitrary interval right-hand sides and zero solution coordinates are covered. Full exact tests checked 60 promised boxes, all 820 matrix vertices in those instances, and 300 exact primal/dual LP certificates.

**Pass: solved for the canonical inverse-M promise.**

## IV-06 — four real spectral components in dimension three

Source: `manuscripts/IV-06.tex`, Theorem 1.

For `A(a,b)=[[25,a,b],[1,−1,0],[1,0,1]]`, with independent `a in [−166,−16]`, `b in [9,159]`, fresh symbolic expansion reproduces

`det(lambda I−A)=(lambda−25)(lambda^2+6)−d1(lambda−1)−d2(lambda+1)`

under a=−91+d1,b=84+d2. The determinant is affine with no mixed term, so its exact interval range has radius `75(|lambda−1|+|lambda+1|)`.

Direct integer checks reproduce the four nonzero eigenvectors at lambda=−3,0,3,25 and admissible parameter choices. The exact ranges at the interposed values −1,1,12 are respectively `[−332,−32]`, `[−318,−18]`, `[−3750,−150]`, excluding zero. A connected subset of the real line containing any pair of these included points would contain the intervening excluded number. Therefore the four points belong to four different components and the at-most-n conjecture is refuted. Exact component endpoints are unnecessary.

**Pass: solved by a valid independent-entry counterexample**, not a symmetric or coupled interval family.

## Evidence, reproduction and PDF review

The submitted checkers were inspected before running. Working copies in `pr62-run/code/` preserve the frozen snapshots; the outputs are `pr62-run/verification/exact_results.json` and `AV-01_exact_results.json`, with logs at the audit root. The full exact suites passed. Floating point diagnostic and exploratory IV-01 search scripts were not used as proofs or needed to establish these seven results.

`independent_checks.py` imports no submitted verifier and checks fresh exact identities, gaps and canonical preservation. Run with the bundled Python and `PYTHONPATH=/private/tmp/nla-pr-review-20260911/python-deps` in this environment. It writes `independent-check-results.json`.

All 25 final canonical/manuscript PDFs across these two PRs were rendered and all 73 pages inspected. No clipping, formula overlap, missing glyph or unresolved reference marker was found. `pdf-qa/report.json` records original file hashes, page counts and text diagnostics; `pdf-source-rebuild-results.json` records reconstruction from unchanged TeX copies for source/PDF comparison.

All rebuilt PDFs have exactly identical extracted text page by page and no XeLaTeX build warnings. Twenty-three are raster-identical too; the other two have only small vertical-spacing changes on MF-03 manuscript p.4 and IV-05 manuscript p.3. Both pairs were inspected side by side; their mathematical content and legibility are unchanged.

No frozen source, shared integration branch, contributor branch or GitHub state was modified by this audit.


Archival note: local snapshot and runtime paths identify the audit environment. This published record includes review prose, independent check sources and JSON results; transient PDF page images, build trees and copied contributor inputs remain in the local audit archive. The original submissions are identified by the frozen Git commits above.
