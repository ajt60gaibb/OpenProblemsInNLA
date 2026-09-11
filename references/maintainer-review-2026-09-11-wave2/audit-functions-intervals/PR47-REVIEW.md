# Independent mathematical audit of PR #47

Reviewed head: `eb17ccdfcda222bf1801afe06eb53c822cf9bcae` in `ajt60gaibb/OpenProblemsInNLA`.
Audit date: 2026-09-11. Frozen source: `../pr-47/`.

**Disposition: no blocking mathematical error found; acceptable in the stated scopes.** MF-03, MF-16 and SF-01 resolve their canonical targets. MF-14 and MF-15 remain partially resolved. MF-18 contributes an auxiliary real-coefficient theorem; its canonical general complex target remains unresolved. The submitted status distinctions are correct. This is an independent mathematical/agent review with exact computational checks, not proof-assistant certification, human peer review, or certification of novelty.

Every original page from its `## Problem statement` heading through the end is byte-identical to the corresponding published `origin/main` page, including later question sections, definitions and original dated audits. All six IDs and canonical paths are retained. Evidence is in `independent-check-results.json`.

## MF-03 — all-order Padé disk bound

Source: `references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-03.tex`, Theorem 1 and its two lemmas.

The denominator linear system has entries `e_(m+i-j)`. Its determinant is the Schur function for the square partition `(m^m)`, by the dual Jacobi–Trudi determinant. The determinant is strictly positive: the tableau with constant row r equal to r already has positive weight. Cramer's rule replaces column j by minus column 0; moving it past j−1 columns gives the asserted sign `(−1)^j` and the shape `(m^m,j)`. This proves existence and uniqueness of the normalized Padé pair, rather than presuming absence of defects.

For each square tableau, a possible extra bottom row has all entries at least m+1 and is weakly increasing. Dropping the remaining column restrictions can only increase its total nonnegative weight. This gives `b_(m,j) <= h_j(t_(m+1),...) <= S_m^j`. Infinite-variable passage is valid because a tableau weight sum of fixed degree L is bounded by `(sum t_i)^L`; there is no conditional rearrangement.

Writing `B=sum b_(m,j)R^j`, the condition `2 R S_m<1` gives `B<2`, `|Q(z)|>=2−B>0` and `|P−Q|<=B(F(R)−1)`. The latter uses the degree-m truncation of `Q(F−1)` and the triangle inequality. Monotonicity of `B/(2−B)` then yields the claimed disk bound. This controls denominator zeros themselves, not merely poles after cancellation.

For `t_i=1/(pi^2(i−1/2)^2)`, the convex-midpoint integral bound yields `S_m<=1/(pi^2 m)<1/(9m)`. The explicit rational upper bound `f(3)<=6179/2120<35/12` follows from the positive Taylor series and its tail ratio bound `3/56`. Thus for every m>=16 the resulting quotient is strictly below 2. There is no gap at the transition from the finite to infinite range.

I independently constructed Padé pairs by rational linear algebra for m=1,...,16, without using submitted certificate coefficients. All residual equations through degree 2m, denominator lower bounds, and finite disk bounds pass. For m>=2 the stronger finite bound below 39/20 passes. At m=1, `p=1+5z/12`, `q=1−z/12`, and `r(3)=3`, confirming sharpness. The scalar result implies only the asserted spectral-radius matrix bound via spectral mapping, not a matrix norm bound for nonnormal matrices.

**Pass: solved.** The proof does not need to rely on the previously published finite-order lemma, because the exact finite certificates independently cover it.

## MF-14 — degree-42 coverage using seven products

Source: `manuscripts/MF-14.tex`, Theorem 1, seven-product display and equations (1)–(2).

I checked the scheme's degree sequence `2,4,6,10,16,26,42`, its 35 internal parameters and 9 output coefficients, and that every factor uses previously available polynomials only. All 43 output coefficients are polynomial functions of the 44 complex parameters and no uncounted polynomial multiplication is used.

The audited exact verifier differentiates untruncated integer polynomials in each of the 44 directions, deletes the `b22` column, and uses fraction-free elimination with exact-division checks. It reproduces

`det J = −8304099790447595998423664434512844589026004175807386862654720`

and residue 22531 modulo 65521. The parameter values, ordering, selected columns and degree agree with the manuscript. The nonzero integer determinant itself establishes rank; primality of the auxiliary modulus is not essential to that conclusion.

Fixing the omitted parameter gives a square holomorphic map with invertible derivative, so its image contains a Euclidean open set. A polynomial vanishing on that image must vanish identically, proving dominance. By constructibility of a polynomial image and irreducibility of complex affine space, the image contains a nonempty Zariski open set; such a set is Euclidean dense. Thus the ambient coefficient closure contains all degree<=42 polynomials. It does **not** establish exact representability of every polynomial, real Euclidean density, or an upper bound excluding degree 43 or higher.

**Pass: partial only.** The canonical maximality equality remains open, exactly as recorded.

## MF-15 — generalized doubly nonnegative critical exponent

Source: `manuscripts/MF-15.tex`, Theorem 1, Lemmas 2–3 and Corollary 4.

For m=n−2 and kappa=1/4, the nonnegative cyclic-bidiagonal family has characteristic polynomial

`p_e(z)=prod_(i=1)^m(z−i e)(z−1)(z−2)−e^m/4`.

There are exactly two determinant permutation contributions. I independently checked this polynomial and the `(1,m)` resolvent cofactor symbolically for n=3,...,7. The cofactor is `e^(m−1)(z−1)(z−2)`, including the m=1 diagonal case.

For `0<e<=1/(8(m+1))`, at every `u=i±1/4` the product `prod(u−j)` has magnitude at least 3/16; the other positive factor exceeds 105/64. Their product exceeds kappa, so subtracting kappa preserves the opposite endpoint signs. The m low intervals and the intervals `(3/4,1)`, `(2,9/4)` are disjoint and each has a sign-changing root. Degree m+2 forces exactly one root in each and simplicity. The same low-root argument at e=0 and continuity give the limits used later. Therefore this family actually satisfies the GDN hypotheses and does not merely have apparently real eigenvalues numerically.

In the spectral expansion, the low-root coefficients remain bounded because the limiting low polynomial has simple roots; their total is `O(e^alpha)`. For fixed `alpha>2m−1`, this disappears after division by `e^(2m−1)`. At each high root, the characteristic equation exactly removes the small product `(lambda−1)(lambda−2)`. The two limits give `kappa(2^(alpha−2m)−1)`, negative throughout `(2m−1,2m)`. Choosing arbitrarily small rational e is legitimate. Taking alpha arbitrarily close to 2m from below gives the claimed lower bound with the correct quantifier over every admissible critical exponent.

The exact interval verifier for n=3,...,10 was read and rerun. Its rational root intervals are disjoint, positive and sign-changing; degree counting validates them. Integer square roots give outward bounds on the only irrational operation. Every normalized negative-entry enclosure has a strictly negative upper endpoint.

For n=4 the matching bound `CE_4<=4` is exactly [Han–Johnson–Paparella, Theorem 3.3](https://arxiv.org/pdf/1407.7059), whose even-dimensional formula is `(n^2−2n)/2`. I checked that primary source. Hence `CE_4=4`, while the matching upper bound for n>=5 is not established.

**Pass: partial only.** Conventional powers, rational examples and all-dimension lower bound are supported; entrywise powers and general equality are not claimed.

## MF-16 — symmetric word nonuniqueness and threshold

Source: `manuscripts/MF-16.tex`, Theorems 1, 3 and 4 and Lemma 2.

For `B=[[1,4],[4,17]]` and `X0=diag(3,1)`, both matrices are positive definite. Direct multiplication gives `P=[[4783113,6377496],[6377496,8503345]]`, with determinant `3^14`. I independently reconstructed the derivative using the differential of a matrix power at `diag(t,1)` and recovered the exact displayed Jacobian and determinant `−11785057051824`.

The word `X B X^12 B X` is interlaced and symmetric with one fixed positive definite letter. [Armstrong–Hillar, Corollary 11.1](https://arxiv.org/pdf/math/0507306), inspected in the primary text, applies to the negative Jacobian determinant in symmetric coordinates and guarantees another real positive definite preimage. The paper's coordinate order matches the manuscript's 2x2 order. This refutes universal uniqueness over Hermitian positive definite matrices too, since real symmetric positive definite matrices form an included subcase.

For the family theorem I derived the general Jacobian independently and checked its determinant factorization as a polynomial identity using `p=1+(t−1)g`. It is `t^(r+1)(r+2)(ac−b^2)^2 H_r`. Orthogonal diagonalization changes coordinates identically in domain and range, and positive scaling changes the determinant by a positive factor. For r=1,2 all terms needed for positivity are immediate; for 3<=r<=6, replacing `b^2` by the strict upper bound ac leaves a positive expression because

`4gt−(r−2)(t^r+t)=(6−r)(t+t^r)+4 sum_(j=2)^(r−1)t^j>=0`.

The degree-one theorem in [Armstrong–Hillar, Theorem 1.5](https://arxiv.org/pdf/math/0507306) supplies a bounded domain containing all solutions. Since every preimage has a positive nonsingular Jacobian, degree one implies exactly one real SPD preimage. For r>=7 the specified `c=t^((r+1)/2)`, `b^2=(1−epsilon)c`, `a=1` keep B positive definite and give a negative limiting H-bracket whenever `0<epsilon<(r−6)/(2(r−2))`; sufficiently large t supplies a counterexample. The threshold is for this family and real SPD data, not for arbitrary words or an unstated complex uniqueness result.

The stronger three-root result is independently certified by two implementations, both read and rerun: fixed-point intervals multiplying the original word and exact Fraction intervals using the Cayley–Hamilton recurrence. Their positive-x boxes have radius 10^−40, are pairwise disjoint and exclude `(3,0)`. Both prove strict box inclusion and contraction norm <10^−20. The preconditioners are actual inverses of nonsingular rational midpoint/center Jacobians. The determinant-3 parametrization ensures SPD, and agreement of the first two output entries plus fixed determinant and positive (1,1) entry forces agreement of the third entry. This closes the reduction from three matrix equations to two scalar equations.

**Pass: solved.** Both the analytic nonuniqueness route and exact existence-box route are valid.

## MF-18 — auxiliary limiting Riccati rank theorem

Source: `manuscripts/MF-18.tex`, Theorem 1 and Corollary 3, Sections 2–8.

This source assumes real A, real symmetric Q, scalar regularization `i eta I`, a symmetric stabilizing solution with positive imaginary part, and a finite invertible limit. The canonical target instead has general complex C,D,R,P and simple unit-circle eigenvalues. The source and catalog correctly keep this contribution auxiliary and do not assert that it proves that general target.

The Stein identity follows by imaginary parts with `Im(X^−1)=−X^−* Im(X) X^−1`. The displayed quadratic factorization is exact and establishes regularity; its stable part has n eigenvalues including multiplicities even if A is singular. The pencil graph `[I;X_eta]` has an invertible upper block and the displayed eigenvector lift satisfies the pencil equation.

I checked the critical local arguments independently. The function `T(t)=exp(i(theta0+t))A^T+exp(−i(theta0+t))A−Q` is Hermitian for real t. The local analytic eigendecomposition and interpretation of branch zero orders as partial multiplicities are precisely the local statements in [Barbarino–Noferini, Theorem 1.1 and Section 5](https://arxiv.org/pdf/2211.15539). A global single-valued eigenbasis is not needed. Since the perturbation is scalar, each branch solves `d_j(t)=i eta`; rescaling yields distinct limiting roots of `a_j z^ell=i`. Stable roots correspond to positive imaginary t, giving ell/2 stable roots for even ell and `(ell±1)/2` for odd ell with sign ±a_j. Interbranch root coincidences do not remove the independent eigenvectors furnished by the columns of U.

The interpolation normalization uses inverse Vandermonde matrices and converges to Taylor coefficients. The two-variable contour/divided-difference bound is uniform even if branch scales differ. The lifted coefficient chains are a complete canonical root system because the local analytic equivalence to diagonal functions is invertible; prefixes of these chains and the separated interior deflating subspace remain independent. The finite limit is then used in `C0=X B0` to prove B0 invertible. This step is essential and avoids inferring invertibility merely from B_eta invertible.

For different branches, reflected analytic orthogonality cancels the apparent denominator zero, leaving eta times a holomorphic kernel. Thus their normalized mixed Gram blocks vanish. For one branch the surviving Cauchy kernel is positive definite as the Gram matrix of distinct decaying exponentials. Vandermonde normalization gives entry scales `epsilon^(ell−1−k−l)`. Their minimal exponent is 1 for even branches, 2 for negative odd branches, and 0 for positive odd branches. Exactly one positive diagonal entry survives in the last case. The interior block vanishes by the uniformly invertible Stein operator, and positivity kills its mixed blocks. Hence the limiting rank counts positive odd branches. Real symmetry pairs positive/negative odd germs, including at ±1, so it equals half the total number of odd blocks.

The semisimple O(eta) statement follows from analytic simple branch roots and the invertible limiting graph; it is conditional on the same finite invertible limit. Fresh symbolic calculations verify the defective example's Riccati equation, `rank(Im X)=1`, determinant polynomial `(lambda−1)^6/4`, and pencil nilpotent-power ranks 4,2,0 (two blocks of size 3). The source's graph-prefix argument, not these finite equalities alone, identifies the stabilizing limit. Existence/uniqueness background was checked against [Guo–Kuo–Lin](https://uregina.ca/~chguo/simax81470.pdf).

**Pass: auxiliary theorem; canonical general target stays unresolved/partial.**

## SF-01 — Newton and Halley H-matrix preservation

Source: `manuscripts/SF-01.tex`, Theorem 1, closure and resolvent lemmas, functional-preserver theorem, Corollary 5.

For a nonconstant rational function `f=a+bz+sum w_j z/(z+t_j)` with the asserted positive/nonnegative coefficients, its imaginary part has the sign of Im z, so every zero is real; f is positive on the positive axis and has positive derivative away from its poles. Its zeros are simple and nonpositive. Negative zeros give negative residues for `z/f`, which convert exactly to positive weights `w'_j z/(z+s_j)`; a zero at zero cancels, and its remaining constant/linear terms are nonnegative. The positive constant case is handled separately. This establishes the closure operation rather than citing it without proof.

Writing A=D−N and its comparison C=D−|N|, a positive vector with Cv>0 gives a convergent weighted Neumann series for every `A+tI`, including t=0. Termwise absolute domination proves the resolvent inequality. Consequently f(C) is a Z-matrix and, for the common vector `v=C^−1 1`, `f(C)v>0`; thus it is nonsingular M. The same resolvent bound gives positive diagonal of f(A) and the entrywise comparison `comparison(f(A))>=f(C)`. Therefore f(A) is nonsingular H with positive diagonal.

Positive affine initialization lies in the class and the scaled Newton map is a positive sum of f and z/f. The canonical initialization X0=A is included; commutation follows from the functional calculus. For Halley, the parallel-sum identity has the exact coefficients 1/3 and 8/3. The source additionally verifies the actual matrix denominator is nonsingular on the right half-plane, which is needed to rule out unjustified rational cancellation. Arbitrary positive scaling is allowed for structure preservation; convergence for arbitrary scaling is appropriately not claimed.

Fresh exact rational Newton and Halley checks with mixed-sign off-diagonal A and three nontrivial scales each reproduce the entrywise comparison and the same strictly positive common weight. These examples are diagnostics; the argument above establishes all dimensions and all steps.

**Pass: solved**, under exactly the canonical real positive-diagonal H-matrix assumptions.

## Computational and document QA

- `pr47-submitted-certificates.log`: all seven submitted certificate programs passed after source audit, including the independent word-root and polynomial-coverage implementations.
- `independent_checks.py` / `independent-check-results.json`: fresh exact Padé construction, general word-Jacobian identity, GDN cofactors, Riccati/Jordan example, scaled iteration comparison and canonical preservation.
- All final canonical and manuscript PDFs were rendered and visually inspected along with PR62: 25 PDFs, 73 pages total. No clipped text, overlapping formulas, missing glyphs or unresolved reference markers were found. The underlying source and PDF reproducibility comparison is recorded in `pdf-source-rebuild-results.json`.
- Recompiling all 25 unchanged TeX sources with XeLaTeX reproduced identical text on every page with no build warnings. Twenty-three PDFs also reproduced identical raster pixels. MF-03 manuscript p.4 and IV-05 manuscript p.3 have small vertical-spacing differences; side-by-side inspection confirmed identical mathematical content and clean layout in both originals and rebuilds.

No changes to the frozen snapshot, contributor branches or GitHub were made by this audit.


Archival note: local snapshot and runtime paths identify the audit environment. This published record includes review prose, independent check sources and JSON results; transient PDF page images, build trees and copied contributor inputs remain in the local audit archive. The original submissions are identified by the frozen Git commits above.
