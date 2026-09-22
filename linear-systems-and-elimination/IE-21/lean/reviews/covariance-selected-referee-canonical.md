# IE-21 covariance selected-target review addendum

Reviewer: Codex AI agent `/root/canonical_inventory`. Date: 2026-09-22.
**APPROVE** these two exact module versions, with no findings:

- SphericalMGF.lean: `e11bfd291518ac09ce7ee7e6ecc66b40f058ab573ed6d80ee5381e831246bb96`.
- Covariance.lean: `0682c7c65d1d668fefecc20898470ded940a1f2edae7eab2cd5f2f3481e0a88b`.

This extends my four-helper review in covariance-modules-referee-canonical.md. I did not author either reviewed proof module. My earlier statement-draft and matrix/finite/uniform semantic proof authorship remains disclosed; this is not independent final whole-problem approval.

I read every line of both modules. SphericalMGF proves actual exponential integrability by boundedness on the surface sphere, not a default-integral shortcut. Nonnegative energy moments imply centered absolute moments bounded by 4^r r!. Dominated convergence identifies the integrated exponential series; its constant term is 1 and its linear term vanishes by the proved directional-energy mean 1. With q=4|a|≤1/2, the remaining series is at most q²/(1−q)≤32a², hence the integral is at most exp(32a²). This works at a=0 as well as both signs of a and retains n≥2 exactly in the selected theorem. The auxiliary bounds for positive dimension are stronger statements, not additional selected hypotheses. Every moment/integrability premise is discharged using the actual normalized surface law.

Covariance supplies this unconditional spherical MGF theorem to the previously reviewed actual-row transport and finite-net proof. Its literal statement matches the independently frozen covariance_concentration signature, with m≥1, n≥2, 0<t≤1 and the exact coefficient 2·9^n and exponent −mt²/512. The wrapper has no remaining MGF, rank, positivity-of-singular-value, or hidden measure premise.

For bounded review scope, I rebuilt but did not independently repeat the mathematical audits of GaussianMoments and SphericalMoments. Their exact input hashes are recorded in input-hashes.json and match root's nonauthor APPROVE receipts in root-gaussian-moments-review and root-spherical-moments-review. GaussianPolar, SphericalLaw, RowLaw, SphereNet and the covariance algebra/Chernoff modules were independently reviewed by me earlier at these same hashes. Thus the two target-module approvals explicitly rely on the cited separately reviewed moment dependency chain; they do not assert my independent whole-chain mathematical authorship review.

Fresh reproduction used `/private/tmp/nla-ie21-covariance-selected-independent-7_hcivhx` with only independently rebuilt local outputs and pinned package cache. All 16 steps exited 0, with no warnings or errors: Definitions, all 13 required implementation modules, a two-signature harness copied literally from frozen Challenge (without importing it), and an eight-public-declaration transitive axiom harness. Each of those eight declarations uses exactly propext, Classical.choice and Quot.sound. All input source hashes were checked before and after the build, and the four frozen mathematical-boundary hashes remain unchanged. No forbidden placeholder/native/trust-extension token occurs in these two modules. This is local pinned Lean kernel evidence, not the final Linux verifier, actual Comparator run, or whole-problem LeanCert/publication gate.

Raw log SHA-256: `c9329158ee76e639309001364d12fb3d01e9f4b6d34961af2674390f44ffe7da`.
Build receipt SHA-256: `1c1744aefde0bfd5c96d81bbf747d8b90031a63e30c522c365b435fa7b1c7dc3`.
Signature harness SHA-256: `c37ac402a4ab4ffaeb92a2eee3e9277361cee902e03213853371eb2b10eab175`.
Axiom harness SHA-256: `b9346ffedeeb0faead20812158842d97990d1d0f182cae8328bf7d1408ea02c2`.
