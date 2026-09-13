# Independent informal review of TR-09 round 5

Date: 13 September 2026. Reviewer: independent Codex AI agent `/root/tr09_review`, separately delegated from the submission editor. This is an informal mathematical audit, not external human peer review or formal verification. No Lean verification was requested or performed.

## Material and verdict

I read the complete `report/TR09_round5.tex`, including every mathematical proof, and compared its claims with the canonical `tensor-computations/TR-09/README.md`, CONTRIBUTING.md and the recording procedure in RESOLVED.md. I did not use the bundled PROOF_AUDIT as independent evidence. The prior fourth-round report and its staged random-start claim are not certified by this review.

**PASS for the expressly limited supporting theorems below. FAIL for any proposed full resolution of TR-09. Recommended canonical status: retain Open.** These results do not establish even a complete restricted-input instance of the displayed randomly initialized optimization guarantee. They may be submitted as independently audited supporting progress, with their limitations visible. The manuscript itself explicitly acknowledges this distinction.

## Theorem-by-theorem findings

- **Lemma 2.1, reference cancellation: PASS.** In orthogonal last-mode coordinates the Jacobian and every block split into first-mode-vector-valued cells. Each off-diagonal cell has at most two independent directions; the binary schedule selects both on at least one block. Diagonal and exterior cells are removed too. This proves annihilation on the whole tangent space and injectivity of every root design, including when the first-mode matrix is rank deficient but has pairwise noncollinear columns. Fixing the own coordinates of the last two modes leaves an injective Jacobian chart; the remaining kernel consists of component scalings.
- **Lemma 3.1, common-metric projection bound: PASS.** The compression of G to each subspace has least eigenvalue at least 1−d. Its normal equation yields the claimed difference between projections. Telescoping uses G-nonexpansiveness on the left and Euclidean nonexpansiveness on the right, with one norm-conversion factor. The resulting constant and its bound for d≤1/4 are correct; no hidden design-condition-number assumption is introduced.
- **Theorem 4.1, uniform derivative bound: PASS.** The two positive definite ambient mode maps carry every reference block, and the full tangent space, onto the corresponding actual spaces. Their tensor product has metric spectrum in [(1−τ)²,(1+τ)²]. Conjugacy with metric projections therefore applies simultaneously to every block. At τ≤1/(64ℓ), the derivative norm is at most 5/64<1/8. The proof correctly uses the polar maps only in analysis.
- **Corollary 4.2, local nonlinear contraction: PASS.** Nonsingular root block designs give an analytic cycle near each fixed root. Quotienting component scalings gives a chart with norm induced by the injective tensor Jacobian. A sufficiently small chart ball is invariant with derivative norm at most 1/4; the stated 3/4 and 5/4 residual comparison gives 5/12<1/2. The size depends on the root. Unique block minimization respects the virtual rescalings, so no unallowed change of objective is required.
- **Theorem 5.1, smoothing event: PASS.** Orthogonality of each base mode gives centered distinct-column inner products, with the displayed variance bounds uniform over base scales and positive smoothing variance. Chebyshev, the union bound and a Gram row-sum bound give (32r+4r⁴τ*⁻²)/n≤65568r⁶/n. The dimension bound 2¹⁷(r+2)³⁶ makes this smaller than (r+2)⁻³⁰. The arbitrary first mode has full column rank almost surely. This proves a root-local rate event, not probability of reaching the neighborhood from an admissible initialization.
- **Proposition 6.1, shrinking nonsingular neighborhood: PASS.** The stated rotation gives X⁺=A(Q∘Q), with x₁⁺=c²x₂⁺. The displayed mixed-block kernel cancels exactly. The initialization distance tends to zero while all root designs are injective. As stated, A has rank two, so this does not establish a failure-probability result on smoothed full-rank inputs or a negative resolution of TR-09.
- **Theorem 7.1, rational recovery at width 2r−1: PASS.** The compressed pencils have the two asserted similarity forms. Independently chosen row Krylov matrices put both compressed factor matrices into the same Vandermonde coordinates, giving Hankel slices. Their 2r−1 anti-diagonal moments interpolate at fixed distinct real nodes, and the lifting maps recover the original slices exactly. No eigenvalue or root-extraction operation is used. The field-operation cost O(n³r) is consistent with n≥r, including exact reconstruction checking if performed. No bit-complexity or numerical-stability theorem follows.
- **Lemma 8.1 and the finite-grid success bound: PASS.** The elementary polynomial zero bound applies to the compression determinants and pairwise ratio-collision polynomials; pairwise noncollinearity makes the latter nonzero. Conditional on the earlier good event, each independent Krylov row contributes a nonzero degree-r determinant polynomial. The union bound is (r²+4r)/M≤1/4, and the stated independent-bit count is correct.
- **Corollary 8.2, relaxed smoothed recovery: PASS.** Gaussian smoothing gives full column rank in all modes almost surely, so the fixed-input algebraic theorem applies conditionally with success at least 3/4. This is a theorem for the relaxed algorithm class only.

## Independent computational evidence

I wrote a separate standard-library exact-rational checker, `independent-checks.py`, without importing the submission implementation. It passed:

1. A complete n=3,r=2 example of tensor compression, both Krylov transformations, fixed-node interpolation, lifting and exact reconstruction of all original tensor entries.
2. Binary pair coverage and exact squared derivative-bound and smoothing-constant inequalities for r=2,…,128.
3. Three fresh rational rotation parameters for the singular-neighborhood construction.

These finite checks support the audit but do not prove the quantified claims. An initially chosen sketch in my new fixture was singular and correctly caused inversion to stop; replacing it by an invertible sketch produced the reported exact reconstruction. This is an allowed bad draw of the randomized algorithm, not a counterexample to its probability theorem.

I subsequently reran the original unit-test suite and exact checker in a separate scratch copy, using `/private/tmp/ra04-py/bin/python` with SymPy 1.14.0 and NumPy 2.3.5. All 12 tests passed, and `src/verify_exact.py` passed all 25 exact records. The fresh output is preserved separately as `independent-exact-checks.json`; the supplied archive's original outputs were not overwritten. Earlier system and bundled Python attempts lacked SymPy; that environment issue was resolved by the available runtime. I did not rerun the floating-point diagnostics, and their reported counts were not used as proof evidence.

## Submission-edition check

I also reviewed the prepared canonical supporting-results notice and submission README. Their statements that TR-09 remains Open, that no restricted random-start guarantee is established, and that algebraic recovery is outside the permitted class accurately reflect this audit. The attributed TeX edition differs from the audited source only in author/date and review disclosure; the mathematical statements and proofs are unchanged. Affiliation source verification is the submission editor's responsibility, not an additional finding of this mathematical review.

## Resolution-policy comparison

The target requires an explicitly specified ALS or gradient method with factors initially sampled independently of the input, polynomial total arithmetic cost and inverse-polynomial conditional initialization success, for arbitrary base triples with high smoothing probability. The local theorem supplies no quantitative basin-entry probability; full support alone is insufficient. Its orthogonal-base smoothing result also leaves the arbitrary-base quantifier uncovered. The global exact algorithm obtains its factors from tensor-dependent pencils and Krylov transformations and is expressly outside the permitted optimization class. Combining these two results does not repair either missing condition.

Consequently neither Solved nor Solution claimed is supported by this manuscript, and an Open supporting-results notice is more accurate than claiming a complete restricted case as Partially resolved. No permanent identifier, canonical path or original target should change. This assessment does not certify historical novelty or any earlier manuscript in the archive.

Signed: Independent Codex AI-agent reviewer `/root/tr09_review`, 13 September 2026.
