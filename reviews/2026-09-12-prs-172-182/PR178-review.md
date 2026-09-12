# Independent mathematical review of PR 178: IE-16

**Verdict: PASS. No mathematical or target-fidelity blocker found.**

Reviewer: Codex AI agent `/root/audit_spectral_linear/ie16_pr178`, independently assigned to review this submission on 12 September 2026. This is an informal AI-agent review, not external human peer review or proof-assistant verification.

Exact reviewed PR head: `89be234df62de181d27e3954d8ba30b9ab072d63`.
Compared published base: `f41f1f9ffa2171550d4bb795862c6170c4f26070`.
Read-only checkout: `/private/tmp/nla-audit-178`.

The finite counterexample proves the negation of the complete original universal IE-16 inequality. The stronger no-finite-universal-constant theorem is also supported by a complete analytic argument. The proposed **Solved** status agrees with the repository's stated informal-audit policy in `CONTRIBUTING.md`, lines 148–152. Neither theorem should be described as Lean verified.

## Material actually reviewed

I read the base and proposed canonical `linear-systems-and-elimination/IE-16/README.md`, all 605 lines of the publication `solution.tex`, the submitted mathematical source, the source notes and submitted README, all 292 lines of the exact verifier, and the separate 38-line reviewer-check script. I inspected the source differences: publication changes add author, affiliation, date, and PDF metadata; they do not change the submitted mathematics. The original canonical mathematical target remains intact.

I did not use the supplied `INDEPENDENT-REVIEW.md` verdict as evidence. I visually inspected all nine publication solution PDF pages and both canonical problem PDF pages after rendering the existing PDFs into scratch PNGs. The equations, quantifiers, references, and status are legible, with no clipping, overlap, or material source/render discrepancy observed. I did not rebuild the PDFs or run a formal proof checker.

## Exact target and admissibility

The original target asks whether, for every set of (n\ge3) distinct nonzero complex points and every (1\le k\le n-2),

\[
M_k(L)\le (4/\pi)\max_{|S|=k+1}M_k(S),
\qquad M_k(S)=\min_{\deg p\le k, p(0)=1}\max_{z\in S}|p(z)|.
\]

The manuscript's (L=\{\omega^a+10^{-3}\omega^b:0\le a,b\le2\}), (k=4), obeys these exact assumptions. Within-cluster distance is (\sqrt3/1000); cross-cluster distance is at least (\sqrt3-2/1000); each node has modulus at least (999/1000). Thus there are exactly nine distinct nonzero points and (1\le4\le7). My exact calculation gives minimum squared pairwise gap (3/10^6). No uniform positive separation, real spectrum, fixed initial residual across all iteration steps, or dimension-independent location constraint is assumed in IE-16.

A single admissible strict reversal resolves this universal truth question negatively. It need not classify all spectra or every degree. The retained real-spectrum theorem and historical difficulty/importance ratings are compatible with that conclusion.

## Finite analytic counterexample

The Lagrange formula in Section 2 is proved in both directions: evaluating an interpolant at zero gives the lower bound, and prescribing the conjugate phases of the cardinal coefficients attains it. The monic variant similarly extracts the leading coefficient. Positivity and existence of the relevant minima follow from finite-dimensional injective evaluation; the denominators are not assumed positive without justification.

Section 3.1 correctly averages over multiplication by (\omega), reducing every feasible degree-four polynomial to (1+cz^3) without increasing its maximum modulus. Conjugation averaging then makes (c) real. The three cubic images and the two real convex quadratics are correct. At (c_*=-(1+\varepsilon)/D), their common value is (m^2), with one derivative negative and the other positive. The bound (H\ge697/1000>0) holds throughout (0<\varepsilon\le1/10). These signs establish the global minimum, not merely a stationary or numerically fitted candidate.

Section 3.2 exhausts the five-point subsets through occupancies ((2,2,1)), ((3,1,1)), and ((3,2,0)). Bounding cardinal-coefficient numerators below and denominators above has the correct direction. The four terms from the paired clusters give the asserted uniform bound; the three-point-cluster cases give a smaller order-ε² bound. At ε = 1/1000, the exact rational comparisons give

\[
M_4(L)=\frac{3003003000}{1001003001001}>\frac{299}{100000},
\quad B_4(L)<\frac{23}{10000},
\quad M_4(L)/B_4(L)>13/10>4/\pi.
\]

The coarse rational upper bound I reconstructed is approximately 0.002268067675365412, already below 0.0023. The finite proof therefore does not depend on the executable certificate. Section 3.3's limiting ratio (4/3) follows by taking the maximum over a fixed finite collection of 126 labeled patterns; no unjustified exchange with an infinite family is used.

## Actual normal GMRES and initial residual

Section 6 uses the actual diagonal matrix with these nine nodes on the diagonal, so it is normal and nonsingular. Its positive weights (\nu_{a,b}=\mu_{(b-a)\bmod3}/3) sum to one, making (r_0=(\sqrt{\nu_{a,b}})) a unit initial residual. Such a residual is realizable, for example with initial guess zero and right-hand side (r_0).

I independently verified all nine constant residual moduli and all four complex weighted moment identities. They imply the Pythagorean identity for every complex degree-at-most-four polynomial with constant term one. Hence GMRES achieves exactly (m) for this (r_0). Conversely, the same feasible (p_*) gives norm (m) for every unit residual because all its diagonal values have modulus (m). This directly proves the needed worst-case assertion, without relying on an unproved ideal/worst-case interchange. All nine starting components are nonzero, and the distinct-node Vandermonde matrix has full column rank through the relevant Krylov degree; there is no premature-convergence loophole.

## Stronger unboundedness theorem

I checked the complete Sections 4–5 argument separately from the finite witness.

* The upper-bound construction prescribes exactly (3d) Hermite data for a polynomial of degree at most (3d-1). The fixed interpolation map is invertible, its correction coefficients are (O(\varepsilon)), and the rescaled local limits are correct. The monic and normalized residual constructions are distinct and both feasible.
* The lower-bound proof first establishes coefficient boundedness via (3d+2) divided-difference functionals converging to an invertible Hermite map of multiplicities ((d+1,d+1,d)). This supplies the compactness needed later. Local Vandermonde bounds then justify the degree-≤d limits and the factorization (f_0=(z^3-1)^dh). The inherited monic or constant-term normalization gives (\max_j|h(\omega^j)|\ge1), proving both full-set liminf bounds, including zero local leading coefficients.
* For subsets, an occupancy at least (d+2) makes the minimum (o(\varepsilon^d)). All remaining patterns have occupancy ((d+1,d+1,d)). Their leading cardinal sums are ((A_d(U)+A_d(V))/(3^d\sqrt3)). The two choices are independent, and the third cluster has enough points. Finiteness permits taking maxima and inverses. Residual numerators tend to one, which correctly accounts for the difference from monic interpolation.
* Starting from the three roots of unity, the induction uses the inner **monic** ratio and proves both outer ratios approach its multiple (2/\sqrt3). The error allocation is correct. The degree recurrence gives ((3^r-1)/2), cardinality is (3^r), and every finite-depth example is admissible. Scales are chosen only after fixing the inner finite set. Therefore the resulting ratios exceed ((2/\sqrt3)^r-\eta), and are unbounded. No infinite-depth spectrum is substituted for a finite example.

## Independent calculations and source verification

After reading the contributor verifier, I copied it to `/private/tmp/nla-pr178-check/contributor/verify.py` and ran that scratch copy with its output also confined to scratch. It passed all 126 exact subset checks, weighted orthogonality checks, and strict comparisons. Its rational field arithmetic, square-root enclosures, alternating-series bounds, comparison directions, and exhaustive combinations loop are sound for this input. It makes no network requests or shell calls.

I separately wrote `/private/tmp/nla-pr178-check/independent_check.py`, importing no contributor module and representing nodes in (\mathbb Q(i\sqrt3)) rather than the submitted (\mathbb Q(\omega)) coordinates. This independently passed the rational minimax identities, all weights and moments, all 126 subsets, their profile counts (81+27+18), and every supplied squared-cardinal value and 60-digit sum/reciprocal interval. The reconstructed maximum subset value is approximately 0.00225055996555038; the ratio exceeds 1.332998919794758. Floating-point conversions were used only for reporting these decimals.

The [author-hosted primary paper by Liesen and Tichý](https://page.math.tu-berlin.de/~liesen/Publicat/LieTic04.pdf) confirms the nonsingular normal-matrix setting and residual formulation in Section 2, interpolation formula (3.10), and the universal-constant conjecture (3.16), with candidate (4/\pi), on pages 91–92. These match the retained target. The manuscript proves its required interpolation and amplification facts directly rather than attributing its new conclusions to that paper. The [official Simons Foundation profile](https://www.simonsfoundation.org/people/sidney-holden/) supports Holden's stated CCB/Flatiron affiliation. I did not authenticate the original private submission or conduct an exhaustive novelty search.

## Scope and disposition

**PASS for the complete informal mathematical resolution, its stronger theorem, and the canonical status wording at the exact head above.** The numerical enumeration independently supports the finite witness; it does not formally verify the asymptotic theorem. No minimal counterexample size, optimal growth exponent, external human review, or formal verification is established or required for this verdict.

The checkout remained clean at the same head after review. I made no repository or GitHub mutations. Current upstream merge state, integration checks, and final publication actions remain the coordinating reviewer's responsibility.
