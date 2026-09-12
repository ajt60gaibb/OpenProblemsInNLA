# MF-21 primary-source and normalization notes

Checked 12 September 2026 against frozen RESULT.md, SHA256
98eb74a858ad3d2bf5fd0055a92d9c96b9a5e4f4f531972cd429462acb2b44f5.
This is an author/coordinating support note, not the independent-agent review.

The complete target is [Barrera–Böttcher–Grudsky–Maximenko, Conjecture 8.4](https://arxiv.org/pdf/1710.05243), printed page 26, equation (8.4) and the immediately following two sentences. It includes all three parts and every integer m at least 3. Theorem 1.2 on printed page 2 proves the m=2 analogue. The seven-diagonal [follow-up](https://arxiv.org/pdf/2111.07196), Theorems 2.3–2.6 on printed pages 4–6, treats the sixth-order zero; its second-order and local statements are not the full target.

The [2026 survey](https://link.springer.com/article/10.1007/s10958-025-07833-x), section “Beyond the simple-loop class: symbols with zeros of the modulus type,” distinguishes the fourth-order model, existing extreme-eigenvalue results, local second-order expansions, and the sixth-order follow-up. This was checked as source/scope information, not used to supply any missing proof step.

For the sole external Toeplitz input, the [Böttcher–Widom primary preprint](https://arxiv.org/pdf/math/0412269) is version 1, submitted 14 December 2004. Its formula (11), printed page 3, defines the cell indices as the least integer in 1,…,n greater than or equal to nx. Printed page 4, the paragraph before equation (13), explicitly records the L-infinity convergence for the pure symbol |1−z|^(2m). Equation (13) states the more general weighted version. Formula (5) on printed page 2 supplies the Green kernel and its central symmetry. These are exactly the unweighted hypotheses used here.

The normalization in our application is:

$$
k_n(x,y)=n^{1-2m}(A_n^{-1})_{\lceil nx\rceil,\lceil ny\rceil},
\qquad
\int_0^1 k_n(x,x)\,dx=n^{-2m}\operatorname{tr}(A_n^{-1}).
$$

The second equality is immediate from the n cells of length 1/n. The ratio between this trace normalization and (n+2)^(-2m) tends to one. No additional factor of n occurs. To pass from essential-uniform two-variable convergence to the diagonal, use that k_n is constant on each cell square and that the limiting Green kernel is uniformly continuous. Every diagonal point in such a square is approached by points away from the exceptional null set; continuity controls the change in the limiting kernel.

Starting from the source's kernel, the substitution u=1−x/t gives the diagonal and beta integral in RESULT.md, equations (28)–(29). These evaluations are derived in the candidate, not imported as an unexplained trace theorem. The exact checker separately expands the integrand and its diagonal polynomial, and verifies these identities for m=1,…,20. The analytic substitution proves the identity for arbitrary m; the finite checks are supplementary.

The other classical scalar inputs are Euler's even-zeta formula, recorded in [NIST DLMF 25.6.2](https://dlmf.nist.gov/25.6.E2), and Lindemann's transcendence theorem. The original paper is F. Lindemann, “Ueber die Zahl π,” Mathematische Annalen 20 (1882), 213–225, [DOI](https://doi.org/10.1007/BF01446522); the [EuDML record](https://eudml.org/doc/157031) identifies the original article. This note does not claim to have independently reproved that classical transcendence theorem.

No third-party PDF, screenshot, or bulk source text is included in this public-ready support note. The links and formula/page locators identify the actual inputs.
