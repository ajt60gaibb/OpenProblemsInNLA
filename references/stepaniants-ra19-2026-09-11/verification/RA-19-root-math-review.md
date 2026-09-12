# RA-19 coordinating-agent mathematical audit

**Verdict: PASS on the complete frozen candidate.** This is the coordinating agent's mathematical audit, separate from the independent sub-agent report and any publication-conversion check. It is an informal automated review, not external human peer review, a formal proof-assistant certificate, or a novelty/priority determination.

Reviewed source: `RESULT.md`, 19,069 bytes, SHA-256 `475e29760333fc215e80eed33e4729649383d112d585d7cca88a8b669b618c22`. The source was read in full and was not changed during this audit.

## Scope and primary source

The target is the number of complex smooth-locus distance-critical points for generic complex data on the variety defined by determinant zero and one fixed zero entry, with the original bilinear squared Frobenius distance. I checked the authors' current arXiv record, version 2 dated 29 January 2022, and the [primary manuscript](https://arxiv.org/pdf/2010.15636v2), Section 2.2 and Conjecture 5.1/Table 2 on printed page 19. The formula is exactly the canonical target for every integer n at least three. The existing dimension-two exception is retained, and no real-critical-point count or general zero-pattern result is asserted.

## Correspondence and excluded critical points

The determinant restricted to the fixed-entry hyperplane is nonzero and multilinear in each remaining coordinate. A repeated nonconstant factor would have degree at least two in a variable on which it depends, so this restricted hypersurface is reduced. Consequently its smooth points have rank n−1, and the determinant gradient and the matrix unit E11 are independent. Their span is exactly the two-dimensional normal space.

For a smooth critical point, write the residual as the sum of these two normal directions. Its determinant-normal coefficient cannot vanish because the generic completed matrix A(0) is invertible. An isotropic left or right kernel vector would also be a corresponding kernel vector of A(z), forcing the unique singular completion. The nonisotropic-kernel condition there rules this out. Normalizing the two kernel vectors therefore yields a nonzero squared singular value.

I checked the repeated-eigenvalue exclusion: a nonisotropic eigenvector of a complex symmetric matrix splits off an orthogonal invariant summand. If its eigenvalue is algebraically repeated, the complement has another eigenvector at that eigenvalue. The adjugate then vanishes, contradicting smoothness of the plane spectral curve. Thus every relevant eigenvalue is simple and the spectral projector is regular, with denominator P_lambda nonzero.

Conversely, at every common solution P=E=0 the proof excludes both the singular completion and the zero eigenvalue. The projector construction has rank n−1 and satisfies the fixed-entry condition exactly. Failure of smoothness would force both kernel directions to be e1 and hence the first-row off-diagonal data to vanish, which is excluded. The construction yields a normal residual and hence a distance-critical point. The projector, rather than a chosen square root, makes the correspondence one-to-one.

For clarity in assessing the local scheme argument, the forward map is also regular on each ordinary normal-bundle chart. Let C(X) be the nonzero determinant-gradient matrix. Choose an off-(1,1) coordinate at which C(X) is nonzero; the coefficient gamma of C(X) is the corresponding residual entry divided by that entry of C(X). Then A=X+gamma C(X), z=A11 and lambda=trace((A−X)(A−X)^T) are regular local functions. These are the inverse of the displayed regular projector map on the good open set. No unproved square-root selection or set-theoretic multiplicity identification is needed.

## Spectral polynomial and degree calculation

Eliminating the lower coordinates in the symmetric linearization gives

\[
fP=\lambda F_bF_c-(fz+g)^2.
\]

The double-pole terms cancel at each simple root of f, so h is a monic polynomial of degree m+1. The squarefree polynomial on the right proves spectral-curve smoothness away from f=0; at f=0, P_z=−2g is nonzero.

I independently checked the polynomial division yielding alpha and beta. The cubic-to-linear resultant replacement contributes the factor (−f)^2; the denominators contribute f^(−4). Thus the exact Sylvester resultant is

\[
R=(h\alpha^2+2g\alpha\beta-f\beta^2)/f^2.
\]

This is a polynomial identity; the division by f^2 is not an informal removal of solutions. Writing h=lambda f+r cancels the degree-2m−1 terms of fr'−f'r and gives degree(alpha) at most 3m−2. The leading coefficient of beta is G: the three leading contributions are −G, −2(m−1)G and 2mG. Hence −f beta^2 has strictly higher degree than the other numerator terms, with nonzero leading coefficient −G^2. The resultant has degree 5m−2=5n−7 in every admissible dimension.

At a root of f the homogenized quadratic has its extra point at infinity, but the homogenized cubic takes the nonzero leading value −f' there. The explicit finite-point exclusion therefore makes the resultant nonzero at those roots. Elsewhere its roots represent ordinary finite common solutions. The g,h coprimality condition excludes z=0, so P_z=−2zP_lambda is nonzero at each common solution. This justifies the local two-branch resultant multiplicity count, even if distinct pairs happen to share their lambda coordinate.

## Generic reducedness

The translated normal bundle of the smooth constrained variety is smooth of dimension n^2. The nonconstant, finite-degree resultant and the established point correspondence give finite generic fibers over the data. Its dominating components have separable finite function-field extensions in characteristic zero. Removing the proper images of the exceptional loci gives reduced generic fibers; nondominating components do not contribute to generic data.

The constrained normal correspondence is locally obtained from the ordinary corank-one correspondence by the transverse condition X11=0 and the free coordinate u11. The exact equation is X11=E/P_lambda. Smoothness and the regular inverse maps above identify the local equation scheme with P=E=0, so reducedness applies to the actual intersections counted by the resultant. It follows that the resultant degree counts distinct critical points, not merely an unverified scheme length.

The generic diagonalization of the lower block does not restrict the target to a special class of data. The orthogonal changes preserve both the bilinear metric and the constrained entry. Equivalently, f and P are invariantly defined characteristic polynomials, while h and g are coefficients of P in z; the rank-one secular factors are the characteristic polynomials of the corresponding lower Gram blocks. The exclusions are algebraic and descend under the finite choices in a generic orthogonal singular-value decomposition. The nonempty witness family therefore supplies the required open set for the original full data space.

## Simultaneous nonempty generic set

For D with distinct positive diagonal entries, b=epsilon beta and c=r epsilon beta, with positive beta and positive r different from one, the two secular polynomials have simple positive roots. Their roots cannot agree because the two secular equations would force r^2=1. The roots of g/epsilon^2 remain strictly between the fixed poles, whereas those of h approach the poles and zero; this proves coprimality for sufficiently small epsilon.

I checked the expansions at each root d_i^2 of f. The finite spectral-curve point tends to z_i=−(1+r^2)d_i/(2r), and the limiting stationarity value is f'(d_i^2) z_i(d_i^2−z_i^2), which is nonzero. At the unique singular completion, real kernel norms are positive. For every nonzero singular component, the fixed-entry residual equals

\[
r\epsilon^2\sum_{j\ne i}\beta_j^2/d_j+O(\epsilon^4).
\]

Its leading coefficient is strictly positive precisely when m is at least two. This excludes every remaining spurious singular-completion pair. The zero component is separately excluded by z_* P_lambda nonzero. All exclusions hold simultaneously for sufficiently small positive epsilon for each fixed m; no uniform choice across dimensions is needed.

The same calculation explains the excluded n=2 endpoint: removing its only nonzero component leaves the singular point X=0. This is not a zero-eigenvalue artifact and does not affect the stated all-n≥3 theorem.

## Conclusion

The argument supplies the full target formula with the original field, distance convention, generic quantifier and smooth-locus definition. It does not rely on the source's finite numerical table or on the supplementary exact checker. No mathematical amendment was required by this audit. Independent sub-agent review and final source/PDF conversion checks remain separate requirements before publication.

Signed: `/root`, coordinating-agent reviewer, 2026-09-12T00:48:57.935991+00:00.
