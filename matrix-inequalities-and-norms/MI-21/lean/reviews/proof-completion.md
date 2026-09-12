# MI-21 proof implementation complete — 12 September 2026

**Verdict: complete local Lean proof; frozen for two independent final proof reviews.** This is the implementer's completion record, not an independent referee report. The canonical status is unchanged. Linux Comparator and publication metadata remain pending.

The full three-export `Solution` builds successfully with Lean 4.33.1: 3147 jobs, approximately 30 seconds with the existing pinned dependency artifacts reused. The actual Proof and Solution modules were elaborated during this build. The raw [build log](../verification/proof-build.log) and [command record](../verification/proof-build.json) retain the result; there were no warnings. This was a local macOS arm64 run, not a fresh Linux dependency rebuild.

## Complete mathematical scope

The frozen target still quantifies every positive dimension and number of summands, all positive definite complex inputs, every allowed real parameter, and every unitarily invariant complex matrix norm. The proof exports exactly the three reviewed statements:

1. `NLA.MI21.operatorNorm_isUnitaryInvariant`: the genuine `Matrix.toEuclideanCLM` operator norm obeys all five stipulated norm properties, including independent left/right unitary invariance, in every dimension.
2. `NLA.MI21.counterexample`: all four concrete inputs are positive definite; both aggregate sums are the identity; the actual CFC left expression is the specified rational matrix; the actual right expression is the identity for every positive real `p`; the nonzero complex eigenvector equation, strict eigenvalue gap, true operator-norm lower bound and strict violation all follow.
3. `NLA.MI21.not_geometricMeanNormConjecture`: the complete original universal statement is false, instantiated at the admissible witness and the proved unitarily invariant operator norm.

No smaller norm class, integer-only parameter domain, commutation assumption, candidate-root hypothesis, assumed spectrum, or extra numerical premise replaces the original target.

## Analytic and numerical proof

`geometricMean_eq_of_riccati` proves a generic analytic bridge. For positive definite `A`, a checked inverse `A*K=1`, and a positive semidefinite candidate `X` satisfying `X*K*X=B`, the candidate is the **actual** CFC geometric mean. It uses the real CFC powers `A^(1/2)` and `A^(-1/2)`, proves their two inverse identities, and derives the unique positive square root of the conjugated matrix. Thus the root identity is a proved conclusion, not an informal certificate assumption.

`mean_squared_of_scaled_riccati` uses a positive real scalar square root only to normalize the candidate. Its square cancels analytically, leaving the rational expression `N²/h`. Both means have separate exact inverse and scaled Riccati certificates. The second mean does not rely on an unproved symmetry or unitary-covariance rule. The checked input square roots are likewise actual CFC square roots of positive matrices.

The two rational certificates and their genuine CFC bridges yield the frozen matrix `witnessL`. Its exact nonzero eigenvector `(1,-4)` has eigenvalue `1351000/1350907`. A generic continuous-linear-map argument transports the eigenvector into actual complex Euclidean space and applies the genuine operator-norm bound. The right expression equals the identity directly from the actual aggregate sums and CFC powers of the identity; consequently no interval in `p` is needed.

Only `1 < 1351000/1350907` uses LeanCert, in explicit kernel mode with the minimal point-inequality import. The [actual printed certificate and consumers](../verification/proof-inspection.log) contain `LeanCert.Validity.verify_strict_upper_bound_dyadic_checked`; the lower norm bound, strict counterexample and full negation visibly use that result. No interval subdivision, approximate eigenvalues, numerical matrix square roots, large expansion or native-execution trust is required. Every other finite certificate is exact complex/rational algebra.

## Trust, fidelity, evidence and attribution

All eight internal and three public `#assert_trust kernel` checks passed. Every corresponding `#print axioms` contains exactly `propext`, `Classical.choice`, and `Quot.sound`; see [axiom audit](../verification/proof-axioms.json). Proof and Solution contain no theorem placeholders, custom axioms, unsafe declarations or native tactics, and never import Challenge. Its three deliberate holes remain exclusively in the frozen statement template.

[Source-level signature comparison](../verification/proof-statement-identity.json) confirms that all three Solution declarations have the exact frozen Challenge signatures. This supports, but does not replace, actual Linux Comparator verification. The [dependency record](../verification/proof-dependencies.json) confirms every one of ten package HEADs matches the pinned manifest with no tracked source changes. The original user cache was not changed; this project uses its own APFS-cloned cache.

The two prior statement approvals and all four frozen statement/source-mapping hashes remain unchanged. Full input hashes are in [proof-freeze.json](../verification/proof-freeze.json). The original canonical README, informal proof, status and permanent ID/path were not edited. No commit, push or PR was made by this implementer. Initial stage-one prose in the project README and numerical plan is historical; final packaging must accurately record proof completion and the remaining review/remote-verification gates.

Mathematical counterexample and informal proof: **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Formalization: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. No George email, source-author endorsement or external human peer review is claimed. The proof reuses actual Mathlib CFC, matrix positivity, unitary and Euclidean-operator APIs; no informal manuscript theorem is imported as an axiom.

## Frozen mathematical bytes

| File | SHA-256 |
| --- | --- |
| `NLA/MI21/Definitions.lean` | `18ebd6d65063b6e970d76b60aab6a8a8bc595189e9b8e188895030d2172f1055` |
| `Challenge.lean` | `f7dd628a7635e8860dec64460bd53adfa71ca391eec763391ae1c8e58d1588b4` |
| `NUMERICAL_TARGETS.md` | `4b0582a3c2da02abf7a349e4ab4af682f6b29bf7026bff21d53edff3ab216312` |
| `SOURCE_MAPPING.md` | `1aa408ef570bb889a8aeddf1fca0574f59384d6ebafaa9aed217a7d31e24fed2` |
| `NLA/MI21/Proof.lean` | `7db067a9cc73e3cda027e2e01d664e4b12bf5af84e8f6b3bb10d9bd4de30e9bc` |
| `Solution.lean` | `a30f8dfd1103b6ba1f1aca927e7ef4a92b6fa8ae70658463cdea649378ae1a50` |

The mathematical sources are frozen pending the two independent final proof referees. Any requested mathematical revision will receive fresh build, hash and affected review checks.
