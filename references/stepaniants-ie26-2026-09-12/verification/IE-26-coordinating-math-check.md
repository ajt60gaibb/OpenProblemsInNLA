# IE-26 coordinating mathematical check

Checker: coordinating Codex agent /root. Date: 12 September 2026 (UTC).

**Conclusion: the frozen argument passes this coordinating mathematical check for both displayed targets. A separate independent full audit is still required.**

This is not the independent review: before the candidate was frozen, I supplied an overlapping derivation for the first bound. That contribution was disclosed to the writer and is recorded in the frozen manuscript. I subsequently read the complete frozen proof and checked the second argument, but that does not remove the pre-freeze contribution.

## Frozen inputs and scope

- Candidate: RESULT.md, 20,755 bytes, SHA-256 5ce6d660bb1b22f0c4dec439934e883b3e014708e49a63de2dba2760c939d295.
- Exact mathematical Sections 1–7: 16,618 UTF-8 bytes, SHA-256 0f9222764933df1602163748f6d8c8755f7e45ab9e25139733d2b92851879f55.
- The canonical entry retains N at least 2, odd m=2N+1, arbitrary independently selected shifts in [-alpha,alpha], and the exact square Fourier model.
- The first result uses a single absolute constant simultaneously for all 0<alpha<1/2. The second allows a constant depending on a fixed 1/4<alpha<1/2. No alpha=1/4 endpoint conclusion is inferred.

The manuscript uses nodes as Fourier-matrix rows, whereas writing frequency indices as rows gives its transpose. Singular values, and therefore the norm of the inverse, are unchanged by transposition. The stated equality E=F_0 F^{-1} is correct with the manuscript's explicit row convention.

## Positive-real representation and the first bound

The phase in R is consistent with odd m. In the indexing 0 through m-1, the uniform root angles have sum pi(m-1), an integer multiple of 2pi. Hence P(0)=-exp(ih sum s_j), and R(0)=exp(ih sum s_j/2). Its real part is positive because the argument has absolute value at most pi alpha.

The zeros remain strictly between consecutive half-grid poles along the entire straight homotopy of the shifts. The rational functions are finite at infinity. Thus subtracting their simple-pole kernel expansions leaves a constant; the purely imaginary boundary values make this constant purely imaginary. The coefficients are real, nonzero, and continuous along the homotopy, starting positive. This establishes positive real parts for both R and 1/R without assuming a probabilistic representation.

The kernel residue is -2 beta_j z_j. Comparing magnitudes gives beta_j=cos(pi s_j)/|P'(z_j)|, with positive cosine, and evaluating at zero gives sum beta_j=cos(vartheta) at most one. The resulting Poisson representation is exact.

The radial product comparison is also uniform near both alpha endpoints. Each node's logarithmic perturbation is an integral over a segment of length at most alpha h. The cell-supremum inequality bounds the sum by an L1 norm and h times a total-variation norm. Since t is at least 1/m and h=2pi/m, the latter loss is an absolute constant after multiplication by alpha.

The factor in the exact integral is consistent: the manuscript's K is half the conjugate Poisson kernel, so its L1 radial difference is 2 log[coth(t/2)/coth(T/2)]. This yields precisely exponent 2alpha, rather than 4alpha. The unperturbed quotient (z^m-1)/(z^m+1) is uniformly bounded above and below at the allowed radii. Comparing to the origin gives the final-scale bound with the same exponent.

For an individual cardinal function, applying

    |zeta-z_l|^2 <= r^(-1) |r zeta-z_l|^2

to all factors other than the cardinal's own node supplies a regularized denominator and a total factor at most exp(1/2). This works even when the evaluation point is a node. It does not require a separate minimal-separation estimate.

On a dyadic annulus the Poisson kernel at its corresponding radius is bounded below by a constant divided by the annulus length. Positivity of its weights bounds the annular sum by Re(1/R), and then by 1/|R|. This produces one radial R ratio. The only factor that can diverge as alpha approaches 1/2 is the single sec(pi alpha) from the derivative weights. There is no second weak-type or separation loss in this proof.

The dyadic geometric sum is bounded by C(m^(2alpha)-1)/alpha uniformly as alpha tends to zero; m at least 5 prevents a small-grid logarithmic degeneracy. Concavity gives cos(pi alpha) at least 1-2alpha. Replacing m with 2N+1 changes the bound only by an absolute factor because N is at least 2. These checks establish the full quantified first target.

## Sector representation and local moments

In the product comparison, the linear term of the analytic logarithmic perturbation is ih sum s_j f_z(a_j), while the cell-defined G-G(0) is sum s_j integral_cell f_z. Taylor and quadrature errors are bounded by C h^2 times the sum of cell suprema of |f_z'|. At radius exp(-1/m), that sum is at most C(t_0^(-2)+(h t_0)^(-1)); multiplication by h^2 is an absolute bound.

This verifies the comparison of |B| and |R| without losing a power of m. The mean G(0) is real and contributes only a phase. Differentiating the Herglotz kernel gives an L1 derivative bound C alpha/t_0, so neighboring cell values of |B| and its reciprocal are comparable by an absolute factor.

The branch powers in Lemma 4 are valid analytic functions because they are defined as exponentials of the already-defined analytic G, not by an ambiguous principal power. The bound |Re G| at most pi alpha places their arguments in [-pi/2,pi/2], hence their real parts are nonnegative. This includes the case of an identically purely imaginary constant.

For a small interval, the supporting local arc has a fixed buffer from every considered point. The far kernel derivative integrates to C/ell, and multiplying by angular variation O(ell) bounds its oscillation by C alpha. Consequently one positive baseline works simultaneously for both weights and reciprocal weights over the whole interval.

At depth ell, the local density is supported on length 8ell and its kernel is bounded by C/ell. Thus |G_loc| is at most C alpha, and both sector powers have bounded modulus at that center after dividing by 2alpha.

The disk automorphism is applied to f(rz), with automorphism center exp(-(ell-t_0)) times the center phase. Its value at zero is exactly f(exp(-ell) times that phase), so the normalization does not change the intended depth. The condition ell=qh at least 2pi t_0 ensures this automorphism center lies inside the disk with depth comparable to ell. Harmonic measure on the selected arc has density at least c/ell. This supplies the local weak-tail estimate with factor ell, not an erroneous whole-circle factor.

The functions f(rz), including their automorphic compositions, are analytic near the closed disk. Their real boundary parts therefore lie in L2. The periodic Hilbert weak-(1,1) theorem applies to precisely these functions. For a nonnegative real part, its L1 norm is determined by its center value; the constant imaginary part is bounded separately. Thus the claimed complex-valued weak estimate follows.

The grid transfer uses disjoint cells and cell comparability. The sharp cutoff follows by integrating the absolute conjugate Poisson kernel over the local support: the coefficient of log(ell/t_0) is 2alpha. The exponent is not absorbed into a generic constant. With p=1/(2alpha) between one and two, integration of the weak tail up to C q^(2alpha) gives q^(4alpha), for both signs of the weight. The denominator 2-p is permitted inside C_alpha.

For large arcs, using the whole circle makes the baseline one and the center modulus of both sector powers exactly one. The full-grid estimate with m is comparable to the one with q because qh exceeds a fixed positive threshold. This covers every interval length.

## Fourier matrix and scale summation

The equality of the inverse Fourier norm with the interpolation-matrix norm follows from the unitary normalized equispaced Fourier matrix. No extra square root of m is missing.

Applying the positive Poisson sum at the perturbed node's radial point bounds beta_j by C/(m |R(rz_j)|). Combining this with the exact residue identity, product comparison, and bounded angular displacement gives the asserted derivative weight. Radial distance handles diagonal entries; circle-distance reverse triangle inequality handles off-diagonal entries.

An entrywise bound by a positive rank-one matrix bounds each masked block by its Frobenius norm, at most the product of the two weight-vector norms divided by its scale. Lemma 4 is applied to one interval containing both interacting blocks, so the baseline and its reciprocal cancel. Applying unrelated baselines to the two blocks would be invalid, but the manuscript does not do that.

At each dyadic scale, fixed-length consecutive blocks have only a bounded number of interacting blocks in both row and column directions; the one final shorter block causes no loss. The bound on the matrix of block norms therefore controls the full scale operator. The exponent 4alpha-1 is strictly positive, so summing the scales is geometric and has order m^(4alpha-1). At the excluded endpoint this step would not supply the stated no-log bound.

## Primary sources and verification limits

I read the August 2026 Chen–Lin–Zhang primary HTML, including Theorem 1.4 and the stated logarithmic gap:
https://arxiv.org/html/2608.21960v1 .
The original Austin–Trefethen author PDF was also opened:
https://people.maths.ox.ac.uk/trefethen/perturbed.pdf .

I verified the exact L2-input periodic Hilbert-transform weak-(1,1) statement in Laugesen, arXiv:0903.3845v2, Theorem 12.1, printed p.67, using the primary PDF's text:
https://arxiv.org/pdf/0903.3845v2 .
The requested web screenshot failed, so this record does not claim a successful visual inspection of that source page. The readable primary theorem states the required inequality for all L2 data and positive thresholds.

No finite numerical run is used as evidence for the analytic inequalities. This check is informal, contributed AI-assisted mathematical work; it is neither an independent final audit nor a proof-assistant certificate or human peer review. It says nothing by itself about later competing submissions or final document conversion.
