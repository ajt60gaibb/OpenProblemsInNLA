# PR97 independent mathematical audit

Reviewed head: `04981f27fd4a1117705dd24139fd752fc2bc3459`.
Published base: `16369809e6e600144bd350ab70b7473b652f46f1`.
Review date: 2026-09-11.

**Verdict: PASS for all three complete canonical targets.** TR-06 is proved affirmatively, TR-15 is disproved by an admissible exact counterexample, and both TR-26 reduced-degree formulas are proved for every requested degree. No mathematical blocker or target substitution was found. These are analytic and exact-arithmetic agent reviews, not proof-assistant certificates or external human peer review. The contributor's embedded PASS labels were not used as evidence.

## TR-06: finite mean angular conditioning

I read the entire Markdown manuscript, checked its generated PDF, and compared the model with the retained canonical statement. It differentiates the tuple of individually normalized recovered summands, uses the induced Euclidean tangent/product norms, and integrates over the volume-Gaussian distribution on tensors. It does not replace that distribution by independently sampled summands. The input model and higher-rank target agree with [Beltrán–Breiding–Vannieuwenhoven, Definition 1.3 and Conjecture 1.10](https://arxiv.org/pdf/1903.05527).

The regular-locus step is valid. Generic complex identifiability makes the ordered polynomial addition map generically finite, and characteristic zero supplies a dense regular locus with smooth local inverse branches. Real rank-one parameters are Zariski dense, so this locus has real points and the expected real dimension. Removing the lower-dimensional exceptional image changes no induced-volume integral. The rank-one cone dimension is `1 + sum(n_j-1)`, so the identifiable image dimension is `k = r(1 + sum(n_j-1)) > 1`. Scaling preserves the regular cone, and its unit link is a nonempty smooth semialgebraic manifold of dimension `k-1`.

The key bounded-graph argument is sound. Introducing positive norm variables makes the normalized decomposition relation semialgebraic by elimination; normalized summands all lie on unit spheres, even when unnormalized summands become arbitrarily large. Minimality excludes proportional summands, so the normalized ordered tuples give the finitely many distinct permutation branches. Their derivative norms agree because permutations act isometrically. No global ordering, global one-to-one inverse, or properness of the unnormalized addition map is assumed.

I checked the exact hypothesis of [Hardt–Lambrechts–Turchin–Volić, Theorem 2.4](https://msp.org/agt/2011/11-5/agt-v11-n5-p01-s.pdf): bounded semialgebraic sets of dimension at most `s` have finite `s`-dimensional Hausdorff measure; closedness is unnecessary. For each smooth graph, its area Jacobian is `sqrt(det(I + Dg*Dg))`, which dominates the largest singular value of `Dg`. A disjoint measurable partition subordinate to local graph charts permits the area formula to be summed without double counting. Finite graph volume therefore bounds the integral of the angular derivative over the link.

Finally, positive scaling makes the normalized tuple constant radially, with derivative norm scaling as `t^-1`. The cone volume factor is `t^(k-1)`. The numerator integral factors into the finite link integral times `integral_0^infinity t^(k-2) exp(-t^2/2) dt`; this is finite because `k > 1`. The analogous normalization integral is finite and positive. Thus the complete requested expectation is finite for every admissible format and rank. The proof does not assert higher moments, a format-uniform bound, or finite mean of the ordinary condition number.

## TR-15: negative Hankel inheritance result

The generating vector `(2,0,1,0,2,0,-1)` with `m=3`, `q=2`, `n=2` has the correct length seven and produces the required order-three/dimension-three tensor and order-six/dimension-two tensor. The common-vector conventions and unrestricted odd-lower-order assertion agree with the concluding conjecture in [Ding–Qi–Wei, final Section 4](https://www.polyu.edu.hk/ama/staff/new/qilq/BIT-DQW.pdf).

Direct enumeration of all contraction coefficients gives

`(Ax^2)_1 = (x1+x3)^2 + x1^2+x2^2+x3^2 > 0` for real nonzero `x`.

Every real H-eigenpair therefore has `x1 != 0` and `lambda > 0`. The first-slice matrix has eigenvalues `1,1,3`, an independent exact positivity check. For `v=(0,1)`, direct enumeration gives `Bv^5=(0,-1)=-v^[5]`; the negative eigenpair is exact. This single permitted instance disproves the universal claim, regardless of whether existence of a lower-tensor eigenpair is required.

The manuscript also correctly verifies nonvacuity. At `x=(1,0,t)`, the remaining equation is `2t^4+2t^3+3t^2-4t-1=0`, whose endpoint values at zero and one are `-1` and `2`. A real root supplies a strictly positive eigenvalue. The associated Hankel matrix has negative final diagonal entry, so no stronger positive-semidefinite-associated-matrix theorem is contradicted.

## TR-26: both reduced discriminant degrees

The proof keeps the standard unweighted embedding and bilinear transpose. Its target agrees with [Borovik–Friedman–Hoşten–Pfeffer, Conjecture 3.14](https://arxiv.org/html/2512.06939v2#S3). I independently checked the full proof, including the reduction from the exact homogeneous-Jacobian definition of ramification.

With `m=2d`, the matrix-to-numerator map onto binary degree-`m` forms is surjective by disjoint antidiagonal coefficients. The denominator has `m` distinct roots, none at either coordinate endpoint. The homogeneous Wronskian restricts to `F=N'D-ND'` in an affine chart. Its evaluation functional is nonzero at every projective point, including denominator roots. The incidence is therefore a smooth irreducible projective hyperplane bundle and is exactly the closure of the nonisotropic critical correspondence. The curve has `d-1` independent normal equations; adjoining the Wronskian gives the canonical Jacobian-rank threshold precisely when `F=F'=0`. Euler's radial kernel and changes of local trivialization introduce no extra condition.

At a simple denominator root, `N(r)=0` forces a double Wronskian root. The isotropic image is exactly the union of the `m` distinct evaluation hyperplanes. Away from these roots, the two independent conditions `(N/D)'=(N/D)''=0` form an irreducible incidence of dimension `m-1`; its projection has finite generic fibers, giving an irreducible hypersurface `S`. Length-four interpolation shows `S` differs from every isotropic hyperplane.

The generic-multiplicity analysis is complete. For `m>=6`, independent jets at one or two points show that triple roots or two distinct multiple roots have image dimension at most `m-2`. For `m=4`, the explicit numerator `t^3` gives `F=t^2(3+t^2-t^4)`, with exactly one double root and four simple roots, including no root at infinity. The desired pattern is open, so it holds generically on irreducible `S`. The analogous generic pattern on each isotropic hyperplane follows from its second-order local coefficient and avoidance of the other components.

At a form with one double root and all other roots simple, the discriminant differential is a nonzero multiple of evaluation of the perturbation at that root. Restricted to the numerator family, this is nonzero both at nonisotropic roots (first-jet interpolation) and isotropic roots (simple denominator derivative). Every component consequently has multiplicity one. The degree-`2m-2` binary discriminant has coefficient degree `4m-6`; subtracting the `m` simple hyperplanes leaves `3m-6=6(d-1)`. Pullback under a surjective linear map preserves irreducibility and degree after adjoining kernel coordinates; zero numerators and constant quotients are included as existing cone vertices, not extra components.

## Verification and documents

The shared `independent_checks.py` passes **552/552** exact checks across PR97 and PR101, including six direct TR-15 checks, eight radial Gamma identities, and twelve TR-26 checks. Two independently chosen exact numerator pencils at `d=2,3` give squarefree total discriminants of degrees `10,18`; dividing by the isotropic resultants of degrees `4,6` leaves degrees `6,12`. These finite computations support, but do not replace, the all-degree proof. The submitted TR-15 script was read before execution and passed in an isolated copy.

`source-pdf-checks.json` records **95/95** source/document checks across both PRs. All 203 ID/path pairs are unchanged; every other canonical page is unchanged; these three original targets, references, headings, and historical ratings are retained. PR97's six final PDFs have **19 pages**, all rendered and visually inspected. The complete proof content and canonical statements are legible; no clipping, overlapping text, out-of-page characters, or replacement glyphs were found. PDF hashes and page counts match the submitted record. No shared integration files, GitHub comments, workflow permissions, or remote branches were changed by this review.
