# Remaining Solved targets after reusable-proof search

Independent read-only audit by `/root/inventory`, 2026-10-23. No proof,
statement, canonical page, registry, status or index was edited. This is triage,
not a new Lean, Comparator or CI acceptance claim.

**Use the new complete TR-06 source first. For a disjoint new proof route,
choose TR-26; no other evidence-only full-proof candidate was recovered.**

Live GitHub main remains `5487945e5a72abd952b0c89915915de8cc9b3e65`: 80 Lean
verified / 38 Solved. Integration `d80eaa9910ea9d6ab578839d75bd704647c99e4c`
contains the already audited complete SP-12/TR-14/PF-05 packages: 83 / 35.
PR367 now contains a complete literal TR-06 Target at
`2b049df5e9b15318987f3fa592b1a7c65a0c0057`, superseding support checkpoint
`fa480595`. See `../latest-candidates/PR367_SOURCE_REVIEW_INVENTORY.md`: 609
independent copy/hash/preservation checks pass, and targeted actual Linux jobs
are green with original artifacts available. Original-artifact/raw-checkout/
consumer/Comparator/rejection audit is still required. Its canonical status
truthfully remains Solved; source completeness alone is not promotion.

The live remote listing has 78 branches; all 78 head objects are present among
the 106 fetched remote refs searched. Source-path/blob inventories are retained
in `REMAINING_INVENTORY.json`, reproducible by `audit_remaining.py`. Live open
proof PRs were #365 (RA-05 support), #366 (the integrated three), #367 (complete
TR-06), and historical incomplete #317. No separate complete proof candidate
for another remaining ID appeared in these paths or open PRs. This is a scoped
per-ID live-source search, not a proof that anonymously named or undiscovered
external formalizations cannot exist.

The 34 Targets without a recovered complete proof after recognizing TR-06's
new complete source are:

`AA-01 AV-01 AV-02 FR-10 IE-08 IE-10 IE-12 IE-21 IE-22 IV-02 IV-04 IV-05 MD-06
MF-08 MI-16 NM-03 PF-04 RA-04 RA-05 RA-12 RA-13 RE-05 RE-06 TR-04 TR-08 TR-17
TR-20 TR-21 TR-26 IE-26 MI-31 RA-19 SP-13 SP-14`.

TR-04 is being pursued by another active user chat; avoid duplicate authoring.
RA-05 has eleven accepted support exports, not its complete
`Classification ∧ NegativeAnswer`. RA-19's local candidate is a reviewed exact
contract without a proof implementation. The partial IE-21/IE-22/IV-02/IV-04/
MD-06/TR-04/SP-14 projects do not prove the current literal reviewed full Targets.

## Recommended TR-26 contract gates

The full target requires reduced hypersurface degrees `6*(d-1)` and `2*d` for
every `d≥2`, in the fixed unweighted Veronese embedding, actual full-ideal
incidence/Jacobian construction and bilinear quadratic form. It has no runtime
or randomized-analysis layer. The source reduces it to binary forms with one
specific denominator, making this a more focused new development than the
other exact algebraic geometry candidates. It is still substantial work.

1. Prove the actual symmetric-matrix-to-binary-numerator map is surjective and
   the fixed degree-`2*d` denominator has exactly `2*d` simple projective roots.
2. Identify the actual full vanishing-ideal incidence and canonical Jacobian
   rank condition with a multiple projective root of the binary Wronskian.
   Include infinity, isotropic roots, zero numerator and numerator proportional
   to the denominator; a selected-equation calculation alone is insufficient.
3. Construct the binary discriminant of degree `8*d-6` after substitution.
   Prove its evaluation-hyperplane product has degree `2*d` and multiplicity
   exactly one; prove the complementary factor is squarefree and has degree
   `6*(d-1)`. The `d=2` witness and loss-of-degree/infinity cases need explicit
   treatment.
4. Prove exact zero-set equality with the target's isotropic **image** and
   nonisotropic **closure**, and pull both equations back through the actual
   numerator map with squarefreeness, homogeneity, degrees and kernel retained.

The Target does not demand irreducibility; a direct squarefree-factor proof can
avoid that stronger obligation. The separate independent finite-candidate
triage in `TRIAGE_FINITE.md` supplies exact manuscript references and library
search limits. No TR-26 proof source was found on any fetched ref.

## Gates that prevent treating another candidate as a short close

| Candidates | Exact remaining burden |
|---|---|
| IV-02, IV-04 | Canonical Solved resolutions establish NP-hardness and solver existence iff P=NP. Current reviewed `Target` is **unconditional** polynomial binary-time solver existence. Preserve it and add a separately reviewed exact classification theorem; do not prove an assumed-P=NP implication and promote it as that Target. Actual finite reductions/complexity upper bounds remain to formalize. |
| IV-05, AV-01 | Shorter interval/LP mathematics still requires an actual polynomial binary-time `FiniteMachine`, complete rational encodings, bit bounds and verified LP implementation/composition. No ready LP machine theorem exists in the inspected repository. AV-02/NM-03/MF-08 additionally require genuine all-NP finite reduction infrastructure and the exact source reduction. |
| RA-12, RA-13 | Exact Gaussian-to-Gamma spectral-law transport and coefficient-transfer tail comparisons, with weak thresholds; positive Gamma convolution/mode identities for RA-12, signed bell-shape/smoothing/limit arguments for RA-13. Neither follows from elementary Gaussian moments. |
| PF-04 | Elementary sharp lower witness is insufficient: universal nine-column CP factorization needs deep order-six copositive/face/orthogonality bounds and their imported lower-order results. PF-05 rigidity does not provide them. |
| MI-16, TR-17, TR-20, RA-19 | Exact radical elimination/representation-theoretic moments; CSM/Euler positivity and scheme lengths; Segre discriminant geometry with reduced multiplicities; or uniform critical-count open sets/resultants. Existing contracts or coefficient identities alone are not full proofs. |
| SP-14 | Many finite Fourier/Toeplitz/jet/Wiener lemmas exist, but stagewise compatible inverse control, infinite-limit symbol, two-sided nonextension and unconditional multiplicity/subsequence conclusions remain. Rich source reuse does not close its analytic gates. |
| SP-13 | Dimension-free weak-type triangular truncation estimate, actual Schur/singular-value counting and compact-support spectral-measure convergence without norm bounds. No ready complete formal weak-type theorem was found. |
| IE-21, IE-22, IE-10, FR-10, TR-08, TR-21, MI-31 | Actual spherical/Gaussian/finite-sampling laws and uniform or asymptotic random-matrix/tensor estimates. Existing zero-vector or empty-energy checks are not probability, threshold, optimality or limit proofs. |
| IE-08, IE-12, RE-05, RE-06, RA-04 | Actual finite operational algorithms plus worst-case runtime/query counts and uniform success/error bounds, not an abstract successful-output existence theorem. |
| AA-01, IE-26 | Full accurate-tree criterion and finite decision-machine realization; or both perturbed Fourier interpolation/norm bounds with their distinct constant scopes. No complete reusable Lean source was recovered. |
| MD-06 | Preserve the historical original Target (limit one) and prove its separately named negative/quantitative resolution. Need actual nonsynchronized local-minimum construction and random-cubic-graph probability tending to one; the current abstract event implication is insufficient. |
| RA-05 | All-exponent and all-parameter coreset classification and negative additive answer remain; exact minimum-support and hyperplane reductions are support only. |

Every mathematical ranking here is an inference from the exact target and
available source/library route, not a completion estimate or pre-proof approval.
