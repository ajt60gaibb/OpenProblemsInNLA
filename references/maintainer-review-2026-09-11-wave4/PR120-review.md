# PR 120 — independent MF-22 mathematical review

Reviewed head: `51e8ae1a801d846f3b649d387e5185df6c4cfdfe`.

**Verdict: PASS for the full original mathematical target. No substantive blockers found.** The proof establishes eventual invertibility and kappa_2(H_n(rho)) <= K_rho n for each fixed rho>0, including rho=sqrt(10), for the exact original uncorrected Toeplitz truncations. Integration, regenerated catalogs and document QA remain with the coordinating agent.

## Scope and original target

Read the complete 482-line canonical `matrix-functions-and-stability/MF-22/solution.md` and the original target from fetched origin/main. The canonical Statement section is byte-identical against origin/main, including every coefficient block, the j-k index convention, all quantifiers and the no-corner-corrections requirement. No registry ID or canonical path is changed.

Directly checked primary source https://arxiv.org/html/2608.24151v1 : equation (5.22) agrees with all four B blocks; the coefficient display following equation (5.32) agrees with all four C blocks; Proposition 5.14 contains the stated quartic; the paragraph following Figure 9 identifies the open polynomial-growth regime. The proof does not assume any general determinant-root criterion is sufficient for finite-section conditioning. It proves the missing boundary estimate for this exact family.

## Independent analytic reconstruction

1. **Recurrence and boundary conditions (solution.md lines 17–111).** Multiplied every canonical block by 80 and checked the two equations separately. For row j the only forward variable is u_(j+1); the C/B structure indeed eliminates v_(j+1). The only out-of-range variables are u_-1, v_-1, v_-2 and u_n. Thus the prescribed initial state e u_0 and single terminal condition e^T w_n=0 reproduce all finite Toeplitz equations without replacing corner entries. The matrix L has determinant 24(30-r²-10ir), nonzero for all r>0.

2. **Generating function and coprimality (lines 113–256).** Independently summed the homogeneous recurrence using u_0=1 and zero negative-index values. This gives the displayed 2-by-2 generating-function system and U=N/d. If N and d share a root, either h=ell=0 or Ah=B alpha; these cases exhaust the algebra because A is nonzero. The quadratic resultant's strictly positive real part excludes the first. The second reduces to the displayed nonzero rational candidate z0; the two real polynomial components of N(z0) cannot both vanish because 70R+867I is strictly negative for y=r²>=0. No real-only root restriction has been introduced: this excludes common complex roots.

3. **All characteristic roots (lines 258–377).** Independently checked the Cayley interpretation, including its omitted point t=-1. Away from r=sqrt(10), the real cubic has one real and two distinct conjugate nonreal roots. Its values at ±i are nonzero, so no finite/nonzero correspondence is lost. At r=sqrt(10), the quadratic has negative discriminant and the remaining t=-1 root is simple; q'(-1)=-100ir. Also q(1)=120ir excludes a repeated root at t=1. Consequently all four eigenvalues are simple, with exactly one strictly outside the circle. The reduced denominator degree argument correctly identifies det(I-zT)=d(z)/a. Coprimality then forces gamma=e^T Pi e !=0 for the outside eigenprojector.

4. **Eventual invertibility and Green estimate (lines 379–474).** Reconstructed the solution of the two-boundary recurrence. Since a_n=gamma lambda^n+O_r(1), its denominator is nonzero eventually and d_n=1+O_r(|lambda|^-n). The rank-one identity Pi e e^T Pi=gamma Pi removes the leading growth in the Green blocks. Each of the three mixed terms has a nonpositive lambda exponent. For ell<j, the sole remaining unstable term is lambda^(j-1-ell)(1-d_n^-1), uniformly bounded since j<=n; for ell>=j, its exponent is already negative. Thus all Green blocks are uniformly bounded for fixed r. Both coordinate families are recovered (u_j from w_j and v_j from w_(j+1)), yielding the stated sqrt(2) C_r n inverse norm bound. The finite block-shift norm estimate gives uniform ||M_n|| and completes the O(n) condition-number bound. Constants need not be uniform in r, precisely as the target allows.

The conclusion depends on no unproved spectral-gap uniformity, no numerical root matching, and no neglect of unstable-mode cancellation. Finite exceptional small n are permitted by the unchanged target.

## Checks performed

- Inspected both submitted mathematical scripts, `independent_exact_check.py` and `verify_exact_algebra.py`, before execution. They use local Gaussian-integer polynomial arithmetic and write only local verification JSON. Fresh runs both PASS. The first verifies 31 identities, including canonical coefficients, numerator/denominator, resultant, coprimality elimination, Cayley transformation, discriminant and direct characteristic polynomial. Logs are `pr120-submitted-exact.txt` and `pr120-submitted-exact-algebra.txt` in this audit directory.
- Wrote a separate numerical checker, `check-mf22-independent.py`, which constructs M_n directly from the original coefficient blocks and builds its recurrence by solving those block equations rather than copying the manuscript scalar entries. Across eight positive parameters (0.001, 0.1, 1, sqrt(10) and adjacent values, 10, 100), all 64 finite-matrix checks at n in {1,2,3,4,8,16,32,64} pass. For n<=4, the recurrence Green matrix matches the direct inverse with maximum relative error 5.12e-12. Characteristic-root classification and quartic residuals also pass. Output: `check-mf22-independent.json`.
- Numerical checks are supporting diagnostics; the all-parameter eventual theorem is justified by the analytic argument above.

No source or branch edits, review posting, pushing, or merging were performed. All exports and check outputs are confined to `/private/tmp/nla-review-trace`.
