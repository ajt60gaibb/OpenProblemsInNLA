# PR 122 — independent IE-02 mathematical audit

Reviewed head: **53dd2d078222d2346ffa20a05e602f9ae1766eef**.

**Verdict: PASS for the complete original complex Jordan-block target and the stronger triangular-Toeplitz affine minimax theorem. No substantive blockers found.** Integration, catalogs, safeguard CI and PDF QA remain with the coordinating agent.

Read the complete 373-line canonical `linear-systems-and-elimination/IE-02/solution.md` and the original canonical target from origin/main. The entire original Problem statement section is byte-identical. It quantifies over complex polynomials, complex unit vectors, all n>=2, every 1<=k<n, and every nonzero complex lambda. The new theorem covers exactly these quantifiers. Status Solved is justified; no divisibility or eigenvalue-regime case remains unresolved within this target.

## Primary theorem checked directly

Opened the primary publisher PDF of Courtney and Sarason, *A mini-max problem for self-adjoint Toeplitz matrices*, Math. Scand. 110 (2012), 82–98:

https://www.mscand.dk/article/download/15198/13193/34699

Section 1, printed page 82, defines the matrix as a general complex Toeplitz matrix of size N+1, identified with compression of multiplication on polynomials of degree at most N. Theorem CF, Section 2, printed page 84, explicitly applies when that matrix is **lower triangular** and gives a minimizing multiplier equal to the operator norm times a finite Blaschke product of order at most N. Thus N=n-1 gives exactly the compression representation used in the proof. The title's self-adjoint qualification does not restrict Theorem CF; no realness, invertibility, nonzero diagonal or simple-singular-value hypothesis occurs there. Only its existence statement is needed.

Also directly checked the original Jordan-block source and its complex polynomial/vector definitions and introductory conjecture:

https://www.karlin.mff.cuni.cz/~ptichy/download/public/TiLiFa2007.pdf

The canonical target deliberately specifies complex starting vectors, including when lambda happens to be real. The submitted proof establishes that target; this review does not silently add a real-starting-vector requirement from the historical source's convention for real matrices.

## Independent reconstruction of the proof

**Maximal singular subspace (Section 2).** For t=||T||>0 and T=t Pi_n M_B, innerness gives ||Bf||=||f||. Equality in the compression contraction holds if and only if Bf already lies in H_n. This is exactly the top right singular space, since t²I-T*T is positive semidefinite. Writing B=a/b with coprime polynomials, Bf=g polynomial is equivalent to af=bg, hence f=bh and g=ah. The condition deg a=d forces deg h<=n-1-d. Conversely this same bound places both ah and bh in H_n because deg b<=d. Therefore the parametrization describes the whole top singular space and its multiplicity, rather than only some maximizing vectors. Zero Blaschke roots, which lower deg b, cause no lost cases; d=0 and d=n-1 are both covered.

**Scalar factorization (Lemma 3).** For a nonzero, nonconstant nonnegative trigonometric polynomial with effective degree ell, z^ell Q has degree 2ell and a nonzero constant term. Its roots occur in reciprocal-conjugate pairs; unit-circle zeros have even multiplicity by nonnegativity and local analyticity. Selecting half the roots with multiplicity produces a polynomial h0 of degree ell whose reversed-conjugate product has the same roots as z^ell Q. The resulting proportionality constant is positive real by evaluation at a point where Q>0. This proves the needed degree bound without increasing dimension. Zero, positive constant, repeated roots and unit-circle-root cases are valid. Zero weights are harmless.

**Simultaneous complex preservation (Lemma 4).** Let f_nu=b h_nu and factor the positive convex mixture of |h_nu|² as |h|². Then f=bh stays in the same top singular space. Integrating against |b|² preserves its unit norm. Because ah lies in H_n, orthogonal projection can be removed in

    <Tf,R_j f> = t <ah, Pi_n(r_j b h)>
                 = t integral overline(a) r_j b |h|².

The projection need not be removed from r_j b h itself, and this expression does not require that product to have degree below n. The common pointwise modulus-square identity preserves this integral for every symbol r_j simultaneously. The inner-product convention is linear in its second argument; t is positive real. Thus both real and imaginary parts are preserved, which is sufficient for every complex GMRES orthogonality equation. This is stronger than preserving only a real directional derivative.

**Optimality (Lemma 5).** The top-singular-space unit sphere is compact, so its finite-dimensional complex moment set and convex hull are compact. If zero is outside the hull, strict separation in R^(2k) yields a direction D in the complex span with uniformly positive Re<Tf,Df> on all top singular vectors. Every real linear functional on C^k has the required Re(sum c_j z_j) form, so there is no conjugation restriction. Continuity extends this positive lower bound to a sphere neighborhood. The compact complement has a strict gap below t² in ||Tf||², because all norm-attaining vectors are already in the neighborhood. The exact squared-norm expansion for T-epsilon D therefore lowers the operator norm uniformly on both parts for sufficiently small positive epsilon. If the complement is empty, the neighborhood estimate alone applies. This proves the convex combination condition without differentiating a nonsmooth largest singular value or assuming simplicity.

**Minimax and Jordan reduction (Section 5).** A best approximation exists in the closed finite-dimensional affine matrix space, independently of dependencies among its spanning matrices. The zero minimizer case is explicitly handled. Otherwise the convex combination from Lemma 5 becomes one unit top singular vector via Lemma 4. Its residual is complex-orthogonal to every allowed direction, so the Pythagorean identity proves that it realizes the operator-norm minimum as its least-squares minimum. The universal reverse minimax inequality completes equality. The constructed vector also establishes attainment of the outer maximum; for any fixed vector the inner minimum is a distance to a finite-dimensional closed image space.

Unitary reversal takes the original upper Jordan block to lambda I+S without changing lambda's phase. Its powers are lower triangular Toeplitz. With Y=I and X=span_C{A,...,A^k}, residual matrices are exactly p(A) with deg p<=k and p(0)=1. No matrix doubling or change of dimensions occurs. The separate observation that the ideal residual cannot vanish for k<n follows from the minimal polynomial and is correct, though not required by the stronger theorem.

## Independent checks and scope

No submitted executable proves the mathematics: the added scripts concern publication/source checks and public-network audits. Inspected `check_submission.py`; it checks preservation and formatting, not the analytic theorem. No submitted script or network audit was executed for this review.

Wrote an independent numerical check of the decisive singular-space/factorization construction in `pr122-preservation-check.py`, with output `pr122-preservation-check.json`. It constructs finite Blaschke products and their compressed Toeplitz matrices, forms convex mixtures of four normalized maximizing vectors, computes a scalar spectral factor, and verifies preservation against **all n lower-shift powers**, spanning every triangular-Toeplitz direction. All **176 cases** for n=2,...,9 pass, including constant Blaschke products, maximal degree, zero Blaschke roots (singular T and lower degree b), and repeated roots. Maximum factor-coefficient discrepancy: 7.54e-15; maximum complex moment discrepancy: 4.83e-15. Explicit constant/zero and unit-circle-root polynomial cases also pass. These are supporting diagnostics, not the universal proof.

No mathematical correction is necessary. No repository edits, remote mutations, posting or merging were performed. Evidence is confined to `/private/tmp/nla-review-trace/pr122*`.
