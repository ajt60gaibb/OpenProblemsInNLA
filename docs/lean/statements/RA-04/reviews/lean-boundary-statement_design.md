# RA-04: independent final Lean-boundary review

Reviewer: /root/statement_design (OpenAI Codex AI agent), 2026-09-28.
Verdict: **approve** for these bound bytes.

## Fidelity reasoning

1. The live source and full implementation notes were read against the approved specification and complete canonical original. Target is closed, chooses one positive real C before all n,d,b,k,A, and retains exactly 1<=b<=k, padded rank<=actual matrix rank, positive block gap, and 0<epsilon,delta<1/2.

2. The pinned singularValues definition was inspected: it is the descending square roots of eigenvalues of the adjoint composition, counted with multiplicity and zero-padded. The positivity/support lemmas identify exactly the first map-rank many positive values. Matrix.toEuclideanLin is toLpLin 2 2, and Matrix.rank is the range dimension of actual matrix multiplication; Euclidean reindexing preserves this rank.

3. BlockCount=(k+b-1)/b is the required natural ceiling for b>=1; k>=1 implies m>=b. BlockGap uses a separately explicit empty value one and otherwise the real infimum of a nonempty finite range at all indices i<m-b. Since m<=rank(A), all denominators are positive and the finite infimum is precisely the source minimum.

4. StepCount applies the actual Nat.ceil to C*((t/sqrt epsilon)*log(2/gap)+(1/sqrt epsilon)*log(n/(delta*epsilon))). The pinned natural ceiling bounds inspected have the intended nonnegative-ceiling meaning. The domain makes this expression positive, so no negative clipping changes the original q. No iteration offset, altered factor, consecutive gap or spectral ratio appears.

5. GaussianLaw is the actual finite product measure of gaussianReal 0 1 over Fin n x Fin b. The pinned Gaussian parameter v is variance; v=1 gives standard normals. DrawMatrix merely bijectively reindexes those entries. No input-dependent starting law or unmentioned randomness occurs.

6. KrylovSpace takes the span of all vectors (A*A.transpose)^j applied to each actual G column for j:Fin q. IsKrylovBasis checks the complete column span equals that subspace and explicit Euclidean column orthonormality. Every finite-dimensional such subspace has a basis, including dimension zero; no arbitrary semantic carrier or full-rank draw promise can make the universal output relation vacuous.

7. RightSpectrum imposes nonnegative antitone eigenvalues, square column orthonormality and the complete coordinate equality B^T B=V diag(lambda) V^T. Square orthonormal columns give an orthogonal full basis, so this describes every actual ordered right spectral decomposition including signs, ties and zero eigenvalues. Truncate computes exactly B times the projector onto columns with index<k.

8. Success ranges over every natural basis width, every correct Z and every legal spectral decomposition of Z^T A, then applies GoodOutput to the actual Z*Truncate output. This implements the reviewed arbitrary-valid-choice convention, never a favorable selected decomposition. Existence of the bases and decompositions is a mathematical fact, not a new assumed target premise.

9. GoodOutput conjoins induced Euclidean spectral error, full sum-of-squares Frobenius error and all ordered right-vector energies for that same output. FrobeniusTail sums every singular value with k<=index<min(n,d). Zero-based index k is sigma_(k+1); its square multiplies epsilon in the energy bound. The vector uses A times a right column W and the full squared norm. The domain gives k<=d, so i:Fin d with i.val<k covers exactly all k requested vectors.

10. SpectralNorm uses the continuous-linear-map norm of the genuine Euclidean matrix map. The pinned toContinuousLinearMap keeps precisely the same action. None of the matrix function-space, entrywise, Frobenius or squared spectral norms is substituted.

11. The single Gaussian event includes all three guarantees and all legal choices, and its measure is compared with ENNReal.ofReal(1-delta). This retains per-input success probability and common C without separating events or degrading the failure probability. Rank=k, zero optimal tail, t=1, nondivisible k/b and exceptional Gaussian draws all remain.

12. The actual local import closure is Infrastructure only beyond pinned external dependencies. Its command verifies a safe closed Prop definition and permits only propext, Classical.choice and Quot.sound. The module selects leancert.trust=kernel and invokes both statement and trust checks on Target. No target axiom or proof appears.

13. The live/frozen sources match exactly under only the standard comment and namespace change. The author-local root receipts bind their current hashes and show successful live/frozen compilation and a real rfl identity theorem, all reporting only the standard three axioms. This reviewer inspected those outputs; it did not independently execute Lean or claim a Linux Comparator pass.

## Pinned external definitions inspected

- Mathlib/Analysis/InnerProductSpace/SingularValues.lean: ce8193fcd5d226845a71f66b8ca7ad385358916a6e0e688745410ac412ed5c81; Actual zero-based singularValues, descending ordering and support/rank correspondence.
- Mathlib/Analysis/InnerProductSpace/PiL2.lean: 1f9827b2db67213c725a2dcc3fec52a87772966d1fbd3fc6857a019dbd7a6053; toEuclideanLin=toLpLin 2 2 and actual matrix action.
- Mathlib/Topology/Algebra/Module/FiniteDimension.lean: 4e5ae8beb3a56ca35b98e0c56fc0c80ecf749e8c9107bdb3b4c86ef809e48fe9; toContinuousLinearMap preserves the linear action.
- Mathlib/LinearAlgebra/Matrix/Rank.lean: 67b4fa7bee02c1806f29562718bfb34c0e1f40af5ec6a91ef91cc33610657491; Matrix rank as dimension of actual multiplication range.
- Mathlib/Probability/Distributions/Gaussian/Real.lean: f86827f9c60d435c5dfeffee1ac6d95f5a953c98703bdc1c653a368c23a2365b; gaussianReal and standard normal mean/variance convention.
- Mathlib/MeasureTheory/Constructions/Pi.lean: 8751b21ac855f1a7b7c63258e8325f75b6fc236d360758b822ddf54597b118bf; Actual finite product-measure construction.
- Mathlib/Algebra/Order/Floor/Semiring.lean: 89cec8d921ee572258917b08f64efc19abe2922fb363e5b0af072c231c9ab7d3; Nat.ceil order characterization and nonnegative ceiling.

## Bound inputs

- docs/lean/statements/RA-04/IMPLEMENTATION_NOTES.md: 8d7bb306fb23c9dbcce84ffb84f9d6905d32899b811b6a35523d37d0b6087d0a
- docs/lean/statements/RA-04/NUMERICAL_TARGETS.md: b274c4e9a2d719dd02586a8f4345d877917f30fcf1349fca584ae54f02643204
- docs/lean/statements/RA-04/ORIGINAL.md: a92ba711df188b40f7eba9320f956b53a72b7c61bb09aee5b72f91832027116e
- docs/lean/statements/verification/2026-09-28-clustered-gap/CheckRA04.lean: 9dc898a3509bcc1d01ff1ddd0a827b5256d1ea13db5b919f9ea9d1d1e3ff8072
- docs/lean/statements/verification/2026-09-28-clustered-gap/CheckRA04.log: 4df56f6706a434ea6b8fd6c3173badab3b87db5ca1ba56e7913b6f349ac3f708
- docs/lean/statements/verification/2026-09-28-clustered-gap/NLA-Statements-RA04.lean.log: 7747c5e9b8109396358336804fff08280e3e39bd40b0bcdadd2e418cdef754a9
- docs/lean/statements/verification/2026-09-28-clustered-gap/Reviewed-RA04.lean.log: d593f38f8acd0c20aa9244b2ac35a03bea03b10da3af54efb589ffc2188ccf75
- docs/lean/statements/verification/2026-09-28-clustered-gap/receipt.json: 285ed25fe887aef658c7c02b5453b069b4608d04cfdc6e0a1cd6bbdcb4b32f48
- lean-statements/NLA/Statements/Infrastructure.lean: 8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37
- lean-statements/NLA/Statements/RA04.lean: 8c337afb401e9836d5d42e270de20b49ac0799e2d1e7d176f32ff9c27321357b
- lean-statements/Reviewed/RA04.lean: 2eaaa2ee7b12bbb07a1a70bc119c665c4c4d4cb59e07f133779c2af8e07a1df2
- lean-statements/lake-manifest.json: a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8
- lean-statements/lakefile.toml: 1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40
- lean-statements/lean-toolchain: 3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71
- randomized-and-low-rank-approximation/RA-04/README.md: a92ba711df188b40f7eba9320f956b53a72b7c61bb09aee5b72f91832027116e

## Limits

Independent AI-agent final source-level fidelity review, independent of specification and implementation author /root. Approval concerns these exact mathematical definitions and bound source bytes. Reviewed author-executed build/identity evidence is not an independently executed kernel or CI result. No target truth, measurability proof or numerical probability certificate is asserted.
