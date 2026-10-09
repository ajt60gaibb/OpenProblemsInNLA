# RA-13 independent Lean boundary review

Reviewer: OpenAI Codex AI agent `/root/inventory`, independent of specification author `/root/statement_design` and Lean author `/root/infra_audit`.

Phase: `lean-boundary`. Verdict: **APPROVE** the statement boundary and its fidelity to the reviewed complete original target. This is not a proof of the target.

The entire canonical README equals ORIGINAL.md byte for byte, including provenance, solved status and retained auxiliary results. The declaration addresses the complete original comparison chain, not an auxiliary mode or inflection claim.

GaussianLaw is the actual finite Measure.pi product indexed by Fin m × Fin n of gaussianReal 0 1, hence all sample-coordinate variables have the required joint independent standard Gaussian law. Estimator sums every p,q quadratic-form term for each sample and divides by m; each extremizer uses its own dimension.

SpectralNorm is the supremum of the Euclidean image norm over the Euclidean unit sphere, with squared-coordinate sums and Real.sqrt. For the quantified n>0 the sphere is nonempty and compact and its continuous image is bounded, so no empty or unbounded sSup convention changes the target. Nonzero A makes this norm positive. These are direct mathematical correspondence checks, not newly claimed Lean proofs of those facts.

Trace is exactly the diagonal sum. FrobeniusNorm is the nonnegative square root of the sum of all squared entries. Symmetric and NonnegativeQuadraticForm use all coordinates over real vectors; they are concrete predicates, not assumed semantic callbacks.

Pinned Mathlib gammaMeasure shape rate is volume.withDensity ofReal(rate^shape / Gamma(shape) * x^(shape-1) * exp(-(rate*x))) on nonnegative x. The value at x=0 differs from the strict-positive source branch only on a Lebesgue-null singleton. Thus the actual measure is the required shape/rate law, not scale parametrization. Its existing probability-measure lemma applies to the positive parameters derived from the target hypotheses.

Target quantifies every n>0 and nonzero real symmetric matrix, including indefinite and zero-trace matrices, every m>0 and every real epsilon above the exact displayed threshold. It introduces no PSD or trace-nonzero hypothesis and never divides by trace.

StableRank is FrobeniusNorm A squared divided by SpectralNorm A squared. Extremizer has Nat.floor(rho)+1 coordinates with floor(rho) diagonal entries lambda and last lambda*sqrt(rho-floor(rho)); all other entries vanish. Positivity and 1<=rho<=n follow mathematically from the stated nonzero finite-dimensional input; no extra premise excludes a source case.

Threshold is exactly 2*lambda/m + sqrt(2*phi^2/m + (2*lambda/m)^2), retaining the complete displayed expression rather than the inconsistent historical asymptotic sentence.

Comparison conjoins the full two-link chain. The left event is two-sided absolute deviation centered at Trace A; the middle and final events are upper tails, centered respectively at Trace B and phi^2/lambda. Both right probabilities are multiplied by exactly 2 in ENNReal with no capping. Gamma shape is m*rho/2 and rate is m/(2*lambda), and all inequalities are weak.

The current and frozen modules match exactly after the prescribed namespace substitution and one frozen-boundary comment. Every repository-local imported module plus all three package-pin files is bound below. The frozen equality confirms retained syntax/meaning only; it does not prove Target.

Author-provided local macOS elaboration logs were inspected and all recorded source/log hashes were checked. Target logs report only propext, Classical.choice and Quot.sound, and the frozen-boundary identity log reports exit 0. This review did not rerun Lean, and those logs are not a Linux Comparator execution.

## Scope limits

This is an independent mathematical and source review, with inspected author-local compilation evidence. It is not external human peer review, a resolution proof, numerical certification, or an independently executed Linux Comparator run. No numerical calculation is needed to state these symbolic probability inequalities; the retained modules explicitly set LeanCert kernel trust and assert the target boundary.

## Reviewed input hashes

- `docs/lean/statements/RA-13/NUMERICAL_TARGETS.md`: `9cb1d0597b603f7db4576a65120df68e4eafa2e07491905804764094dd01861d`
- `docs/lean/statements/RA-13/ORIGINAL.md`: `16a973ffc9040332e2a521a6a2d2938dcb95df736304185f88ea195a8c78a377`
- `lean-statements/NLA/Statements/GaussianTrace.lean`: `fb2abf78f23834a862954d872a87e05390d11ac472bdd264757f0358d196f4c0`
- `lean-statements/NLA/Statements/Infrastructure.lean`: `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37`
- `lean-statements/NLA/Statements/RA13.lean`: `97df340b6fb8111fa70f1a210634b84f56abec5b82ff625b064a46f7b14d7372`
- `lean-statements/Reviewed/RA13.lean`: `81ba49c5c9b5f2a56103e4d2550136ad2b102f1287a7cf7fde665e5aace21fec`
- `lean-statements/lake-manifest.json`: `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8`
- `lean-statements/lakefile.toml`: `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40`
- `lean-statements/lean-toolchain`: `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71`
- `randomized-and-low-rank-approximation/RA-13/README.md`: `16a973ffc9040332e2a521a6a2d2938dcb95df736304185f88ea195a8c78a377`
- `docs/lean/statements/RA-13/source-lock.json`: `3c358c1a4012489ff81379faafaefb75599dbf74235b8343076936dd8b00f947`
