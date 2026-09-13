# Proof and scope audit

## Common-metric theorem

The proof works with subspaces, not nearly dependent choices of columns. A single mode transformation transports every block space and the full tensor tangent space. Its squared singular values are controlled solely by the two normalized Gram matrices. Weighted projections are conjugate to the actual Euclidean block projections. Telescoping uses nonexpansiveness of each entire weighted tail, avoiding an exponential product of conditioning constants.

The local tensor bound is transferred to factor coordinates only after proving that the Jacobian kernel consists of component scalings. The finite update map is analytic because every root design is nonsingular. The virtual gauge changes no tensor term and is not executed by the algorithm.

**Not proved:** a uniform basin radius for smoothed full-rank triples; an inverse-polynomial probability of entering the basin from an input-independent initialization; a global rate for arbitrary coherence in all three modes.

## Smoothing event

The assumptions are imposed on deterministic bases: B and C have orthogonal columns, while A is arbitrary. Effective column scales include rho and permit zero base columns. Relative second-moment bounds are uniform in all base magnitudes. A union bound gives the stated normalized-Gram event, and full rank of the smoothed A follows almost surely. The event does not depend on epsilon.

**Not proved:** the original random-start guarantee for this enlarged input family. A good local root is not a successful random trajectory.

## Boundary example

Every root design is nonsingular; after an arbitrarily small initial rotation, the first first-mode solve makes two updated columns collinear, and the next mixed design has an explicit kernel vector. The example has a rank-deficient first factor matrix but CP rank three. It concerns the specified singular-abort convention.

**Not proved:** failure on once-smoothed inputs, a random-initialization lower bound, or impossibility for other block conventions.

## Rational benchmark

The algorithm receives only tensor slices, the rank, and random bits. Compressed factors, eigenvectors, and eigenvalues occur only in the proof. Two row-Krylov matrices turn the slice family into Hankel matrices. Fixed real interpolation nodes yield exactly 2r-1 terms. Explicit lifting identities reconstruct the original uncompressed tensor.

The finite-grid proof separately accounts for compressed-factor invertibility, nonzero contractions, distinct pencil ratios, and conditional cyclic-row success. Total failure is at most (r^2+4r)/M. Taking a power-of-two M at least four times that numerator gives success at least 3/4 with a deterministic polynomial random-bit budget in the ideal independent-bit model.

**Disqualifying for TR-09:** the output factors are obtained by data-dependent algebraic computation, not by the required randomly initialized optimization trajectory. A final least-squares fit of the third factor does not repair this issue.

## Exact checks

The positive-definiteness tests certify the entire chart tangent map for each fixture, not randomly sampled directions. Rational reconstruction compares all tensor entries. These tests are finite cases and do not replace the general proofs. The programs are not a theorem prover.

## Earlier work

The orthogonal-reference cell proof from round 4 is reproduced and used. This round corrects an overly broad interpretation of its perturbation warning: coherence need not enter the *derivative-level* robustness threshold when two mode transformations are common near-isometries. The local basin and global initialization warnings remain.

The earlier staged-ALS report is not imported as a lemma, and its full proof has not been independently certified here. No claim that the previous proposed PARTIAL designation is now independently audited is made.
