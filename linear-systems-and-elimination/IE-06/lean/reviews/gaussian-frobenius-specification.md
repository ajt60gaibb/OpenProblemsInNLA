# Centered Gaussian Frobenius concentration: approved specification

The infrastructure/proof agent proposed the following exact theorem to the root
agent before implementing `GaussianFrobenius.lean`. The root independently
approved it on 2026-10-06: “Approved exact GaussianFrobenius signature and plan.
The Frobenius and genuine Euclidean operator definitions match manuscript A1,
threshold exactly2mF²+4xop², dimensions0 covered.”

For arbitrary natural numbers m,n,p and a fixed real n-by-p matrix M, define
`frobeniusSq A = ∑ i, ∑ j, (A i j)^2`. Define `euclideanOpNorm A` as the norm of
the continuous linear map induced by `Matrix.toEuclideanLin A`, from Euclidean
column space to Euclidean row space. This is the induced Euclidean operator
norm, not the entrywise or row-sum norm.

For every real x>0 prove, under the literal nested product standard real
Gaussian law `GaussianNull.gaussianRect m n`,

`P[2*m*frobeniusSq M + 4*x*(euclideanOpNorm M)^2 < frobeniusSq (G*M)] ≤ exp(-x)`.

Probability is an ENNReal measure and the right side uses `ENNReal.ofReal`.
No positive dimension, nonzero M, independence, transformation identity,
integrability, or spectral assertion is assumed in the public theorem.
Zero operator norm implies the zero matrix and an empty strict exceedance event.

The approved proof constructs the Gram matrix M*Mᵀ, proves nonnegative
eigenvalues bounded by the squared induced Euclidean operator norm and proves
that their sum is the exact Frobenius square. Product Gaussian invariance under
its orthonormal eigenbasis is derived from pinned Mathlib's standard Gaussian
map theorems. The previously proved scalar weighted-square MGF transfers to
each row; product integration over the m independent rows and Chernoff yield
the displayed constants. This is the centered case of manuscript Lemma4.1,
not the shifted result and not the remaining main IE-06 probabilistic theorem.

This implementation is written directly against pinned Mathlib. No RRF density
module, manuscript result, custom axiom, `sorry`, or native evaluation is used.
The ordinary trusted logical axioms are independently audited after compiling.
