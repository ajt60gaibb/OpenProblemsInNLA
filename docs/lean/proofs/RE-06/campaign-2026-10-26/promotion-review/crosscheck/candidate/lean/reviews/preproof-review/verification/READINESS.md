# RE-06 readiness and mathematical route

This author preflight finds a faithful route to the frozen target, but substantial new probability and matrix-analysis proofs remain. No RE-06 theorem has been implemented. The accepted existing SVD existence result removes one algebraic prerequisite; it does not prove success, query complexity, pseudoinverse measurability or Gaussian inverse moments.

## Source fidelity and existing reuse

The complete canonical solution is Sidney Holden's 12-page `solution.pdf` and corresponding `solution.tex`, preserved verbatim. Its Theorem 1.1 is affirmative for fully nonadaptive two-sided matrix-vector queries, factor `3+ε`, success at least `0.99`, and explicit `4000000 sqrt(log(2M)) ε^(-2)` queries. Its numerical experiments and informal proof audit remain supplementary source material, not proof certificates. `NUMERICAL_TARGETS.md` and all four retained statement reviews explicitly preserve the zero-optimum, rank-deficient and exact-real operational cases.

The fixed source sets `L=ceil(log₂(2M))`, `r=ceil(sqrt L)`, `η=ε/4`; then

- `s=ceil(32L/(rη)+64/η²)`;
- `k=r+1+ceil(256r/η)`;
- `ell=k+1+ceil(256k/η)`.

The actual frozen implementation uses `Nat.clog 2 (2*(m+2))`, `Nat.sqrt` plus one finite comparison, and real natural ceilings. It precommits `min(n,s+k+ell)` queries. The initial block is unscaled standard Gaussian: dividing all its squared scores by positive `s` yields the manuscript's variance-`1/s` scores and preserves the exact finite minimizer. This normalization must be proved, including `s>0` in the sketch branch.

Supplementary source commit `653b8f1641415f4160811648ff3e23889ba2e136` provides `NLA.Proofs.TR04.SVD.exists_validSVD (B)` with no hypotheses, for every rectangular matrix including zero dimensions. Its `SVDMachine.lean` is byte-identical to the RE-06 published model. `SVDCore.lean` and `SVDTotal.lean`, their independent frozen-nine review binding, source lock and accepted logs/result are copied under `supplementary-reuse/`, with nine exact files in `REUSE_LOCK.json`. These existing proofs may be reused only with their unchanged provenance and a checked import closure. The packet scaffold does not reprove or independently re-review them. A short new proof connecting this existence theorem to the **actual** `exactSVD` choice would establish `svd_total` after authorization.

## Proposed proof decomposition

1. **Finite operational and deterministic matrix layer.** Prove the finite scan attains a minimum with the specified first-tie rule; every actual output lies in the enumerated family; oracle transcript columns equal the required matrix products; the full branch recovers `A` exactly; and query count is exactly `min(n,s+k+ell)`. Prove the source SVD pseudoinverse has the Moore–Penrose identities, uniqueness and compatibility with transpose/full-rank inverse formulas. The target asks for query complexity, not bit complexity or bounded arithmetic work; the exact SVD primitive remains the fixed model primitive, with its validity proved rather than assumed.

2. **Actual stream blocks and Gaussian quadratic Laplace transforms.** Prove the concrete stream offsets are injective and mutually disjoint, and transport the original `GaussianLaw` to the finite three-block product Gaussian law. Obtain invariance under the actual orthogonal SVD rotations and the independent coordinates used in spectral calculations. Prove the one-dimensional square transform, then its finite product version `E exp(-θ λ χ²_s)=(1+2θλ)^(-s/2)` and the corresponding positive transform on its genuine integrability domain. A scalar *linear* Gaussian MGF does not directly discharge this square transform.

3. **Uniform warm-start trimmed-tail guarantee.** For fixed residual `C`, use the squared singular values and the source Chernoff proof to obtain the lower-tail probability `exp(-srη/4)` for energy below `(1-η) τ_r(C)²`. Handle zero tail separately as an empty strict bad event. For the one fixed optimal residual, prove upper-tail `exp(-sη²/8)`. A finite union over all candidates and the actual finite minimum then give `τ_r(A-B0)² ≤ (1+η)/(1-η) * OPT²`. Candidate scores need not be independent; only the three prequeried Gaussian blocks must have the proved product law.

4. **Gaussian rectangular pseudoinverse moment.** Prove full row rank almost surely for an actual `d×p` standard Gaussian matrix when `p>d+1`, and the exact expectation `E ||X†||_F²=d/(p-d-1)`, including `d=0`. The source uses an actual nonzero polynomial minor and absolute continuity; a Schur complement conditions on the other rows, leaving a projector of rank `p-d+1`; Gaussian rotational invariance reduces its squared norm to chi-square, whose inverse moment is `1/(p-d-1)` by the Gamma integral. This requires measurable/integrable expressions and the actual SVD pseudoinverse, not an uninterpreted inverse-Wishart bound. A different proved estimate with the same sufficient constants could be used, but no such replacement has been established in this packet.

5. **Conditional two-sided repair and zero-tail cases.** For fixed residual `C`, construct the range projection of `Y=C*G1`, then prove the source nonnegative majorant `Z=X+V` with error squared at most `τ_r(C)²+Z` and expectation at most `[a+b(1+a)] τ_r(C)²`, where `a=r/(k-r-1)` and `b=k/(ell-k-1)`. The difference `error²-τ²` need not be nonnegative and cannot itself be used in Markov. Derive Markov when the tail is positive; if the tail is zero, expectation zero plus nonnegativity must yield exact reconstruction almost surely.

   The frozen postprocessor uses fixed dimensions `Y*(HᵀY)†*W`, while the manuscript uses a basis `Q` for the actual range of `Y`. Prove equality to `Q*(HᵀQ)†*W` on the almost-sure full-rank restriction of `Hᵀ` to that range. This needs a proved pseudoinverse product law under the relevant full-column/full-row hypotheses, including range rank zero. It cannot be justified from notation alone.

   `B0` depends measurably only on `G0`. The analysis must keep `G1,H` independent after this finite-valued choice under the original law. A finite partition by the selected index followed by product-measure/Fubini arguments can avoid an unnecessary regular-conditional-law construction. It still requires all actual functions/events in those arguments to be measurable or an explicit measurable majorant whose inclusion in the target event is proved.

6. **Arithmetic, probability and literal assembly.** Prove all ceiling/log/square-root inequalities and every denominator's positivity in the sketch branch (`n>s+k+ell` implies the required `r<n`). The source bounds failure by `exp(-8)+2 exp(-16)+1/128+1/524288 < 1/100`. Its count uses `s+k+ell ≤ 66403*r/η²`, `r<3 sqrt(log(2M))`, and `η^(-2)=16 ε^(-2)`, hence the coefficient `3187344<4000000`. Establish the final two triangle inequalities and the exact `(3+ε)` factor. Assemble `OriginalClaim`, `ExplicitClaim` and literal `Target` with no extra hypotheses.

## Measurability and finite-run issue to resolve explicitly

`exactSVD` uses an arbitrary classical choice of a valid SVD. Existence and validity alone do not imply that the selected bases are Borel functions of the matrix. The resulting Moore–Penrose matrix is basis-independent, so one sound route is to prove that uniqueness, identify it with a rank-stratified measurable rational formula (or a limit formula), then obtain measurability of the actual `pseudoInverse`. Another sound route may prove success using measurable explicitly described good events with a pointwise deterministic conclusion for the actual output; any integrations of pseudoinverses still need justified measurable representatives. The target's raw measure notation does not license unjustified conditioning or Bochner integrals.

All lists and matrix index sets in the program are finite, all real ceilings used at valid inputs are finite natural numbers, and every malformed transcript/rank-deficient outcome has an actual specified value. The retained model permits exact arithmetic/comparison/SVD primitives and charges only the finite committed oracle list. A proof must connect these actual definitions to the source's operations; no extra adaptive query or silently changed primitive is available.

## Bounded pinned-library search

The author inspected the pinned local Mathlib source, not current web documentation. `LIBRARY_SEARCH.json` records exact commands, their outputs and SHA-256s of the directly inspected primary files. Useful existing APIs include:

- `ProbabilityTheory.gaussianReal`, Gaussian density/integrability and `mgf_id_gaussianReal` in `Probability/Distributions/Gaussian/Real.lean`;
- `integrable_exp_neg_mul_sq`, `integral_gaussian` and positive-half-line power/Gaussian integrals in `Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean`;
- `iIndepFun_infinitePi`, `iIndepFun.precomp`, and `measurePreserving_eval_infinitePi` for actual stream coordinates;
- `stdGaussian_map` and `stdGaussian_eq_map_pi_orthonormalBasis` in `Probability/Distributions/Gaussian/Multivariate.lean`;
- Gamma PDF, normalization, measure and CDF foundations in `Probability/Distributions/Gamma.lean`.

A case-insensitive search for Wishart/chi-square/pseudoinverse names in pinned `Mathlib/Probability` and `Mathlib/LinearAlgebra` found no directly usable probabilistic theorem; its only match was a comment in `Matrix/NonsingularInverse.lean` saying pseudoinverses are not considered there. This is a bounded search result, not a proof of global library absence. The Gamma file inspected does not itself provide the needed rectangular inverse moment. Gaussian quadratic Laplace, inverse moments, full-rank and conditional repair therefore remain explicit proof obligations rather than an already available imported theorem.

## Evidence and authorization state

`verification/author-scaffold/RESULT.json` records **14/14 expected outcomes**: five frozen project source builds from a fresh temporary source/object tree, one six-signature elaboration, one literal live/Reviewed identity, six separate genuine theorem-hole trust rejections, and the full Challenge's six trust rejections. Seven builds exit zero; seven negative-test commands exit nonzero as required. All ten dependency heads were checked against the frozen manifest before and after. There is no reused project `.olean`, RE-06 proof, independent approval, Comparator result or CI receipt in this author scaffold.

`audit_inputs.py` separately compares the 49 published snapshots to the exact base Git objects, all 217 registry pairs, nine supplementary snapshots/provenance, the SVD model equality and literal six Challenge headers. The packet is ready to request the two independent non-author pre-proof reviews; implementation must wait for their explicit hash-bound approvals. The proof route above identifies remaining mathematical work and is not a claim that those steps have already been verified.
