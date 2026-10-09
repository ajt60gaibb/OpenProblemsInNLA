# Deterministic contraction-supremum Ky Fan functional

Author: `/root/independent_math_review`; coordinator `/root` approved these exact
signatures before implementation. This supports the independently reviewed
A1 alternative contract, without asserting an unproved variational identity.

For A : Matrix (Fin m) (Fin p) ℝ, define

- frobeniusNorm(A) = sqrt(sum_i sum_j A(i,j)^2), with proved equality to the
  flattened Euclidean norm and to sqrt(GaussianFrobenius.frobeniusSq A).
- kyFan(k,A) = sup {frobeniusNorm(Q*A) : Q : Matrix (Fin k) (Fin m) ℝ,
  Spectral.opNorm Q ≤ 1}.

Prove that the supremum set is nonempty and bounded; the functional is
nonnegative and kyFan(0,A)=0. Prove, for every natural k,

kyFan(k,A) ≤ sqrt(k) Spectral.opNorm(A),

and, for 1≤k≤min(m,p),

sqrt(k) Spectral.singularValue(A,k−1) ≤ kyFan(k,A).

For equal-sized matrices A,B, prove

abs(kyFan(k,A)−kyFan(k,B)) ≤ frobeniusNorm(A−B).

For G,H : Matrix (Fin m) (Fin n) ℝ and M : Matrix (Fin n) (Fin p) ℝ, prove

abs(kyFan(k,G*M)−kyFan(k,H*M)) ≤ Spectral.opNorm(M) frobeniusNorm(G−H).

The final deterministic interface will expose the corresponding actual
Euclidean-coordinate Lipschitz property on EuclideanSpace ℝ (Fin m × Fin n),
using its entries directly. Gaussian-law transport is owned by the coordinator.

The proof uses column/row Euclidean norm identities to establish the two
Frobenius/operator product estimates. The lower singular bound chooses the
first k nonzero left singular vectors as the rows of Q, proves contraction
by Bessel's inequality, and computes the resulting row norms from the genuine
forward SVD. If singularValue(A,k−1)=0, nonnegativity proves the target directly.
The contraction supremum gives the Lipschitz inequality by the triangle
inequality and the proved product bound. There is no numerical enumeration,
no caller-supplied spectral comparison assumption, and no claim that this
module alone proves the Gaussian probability estimate.
