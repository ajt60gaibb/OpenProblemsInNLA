# Independent future-column and smoothing review

Reviewer: independent mathematical review agent. Verdict: approved. Reviewed complete source and rebuilt each frozen module independently with the pinned Lean 4.33.1 runtime. All declared kernel trust assertions passed, printed theorem axioms are the standard foundational three, and the builds emitted no warnings or errors. This is a local pinned-cache verification, not a fresh rebuild of dependencies or standalone kernel replay. Receipts and compiler output are retained in `gaussian-future-independent/`.

## GaussianFutureWindow

SHA-256: `f594e4d08ee4bd4fc4d3252f0dea91c22b766e7bd10f3b189442789aaf304262`.

The concrete index equivalence partitions precisely the columns from t onward into t through t+s-1 and the suffix from t+s. It requires only t+s<=n and includes empty windows or suffixes. The split and assemble maps are inverse measurable coordinate reindexings. Their measure-preserving proofs use finite Gaussian product reindexing, sum-product splitting, and the already proved matrix transpose law, with the actual n-by-s Gaussian matrix in the first factor. There is no conditioning assumption.

## GaussianAdaptiveFuture

SHA-256: `16e37b2640d07f8ef3b8c5970e687490769f80f614838093c1feb4d1c14b367a`.

The tested-function integral uses the exact fixed-order conditional law already established by GaussianCoordinates. The Good(T) restriction and the mass factor q(T)^(n-t) are retained. Each fiber upper bound is multiplied by orderWeight, and summing the weights gives one. The arbitrary measurable intrinsic event is restored exactly before summing over actual canonical orders. No factorial union loss is introduced, and auxiliary spectral frames do not need a measurable choice because they enter only pointwise fiber estimates.

## GaussianFutureSmoothing

SHA-256: `58310530cebae91403d0d2aa5cc4e9670c16d25a1773ea9a0160ad035e78973b`.

The literal threshold is 2^s*zeta*(1+sqrt(2s+4x)*sqrt(3exp(2+x/r)/r)). The assumptions include r>0, q<=r, 3r<=s, x>0, a nonnegative row cap, a fixed prefix decomposition E=X+YQ^T, and Q^TQ=I. The event explicitly retains det(A)!=0. For each trailing suffix, the proof chooses the actual subsequent elimination operator J, derives its row-l1 bound and annihilation identity from actual admissibility, and uses exact prefix-column dependence. GaussianSmoothing permits arbitrary J, so no unproved measurability of that intermediate is assumed. The final intrinsic event is proved measurable and integrated over the untouched trailing suffix. The resulting cost is exactly (n+1)exp(-x), with no conditioning on future success.

No source correspondence, quantifier, dimension, singularity, or proof-trust defect was found. These are support results for the final IE-06 proof; they do not alone establish its asymptotic growth statement.
