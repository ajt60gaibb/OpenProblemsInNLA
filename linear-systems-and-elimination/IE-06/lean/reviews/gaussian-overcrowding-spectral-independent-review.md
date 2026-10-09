# Independent review of the A3 spectral event implication

Root read the complete source authored by /root/independent_math_review,
SHA-256 `d72781d59d37fd5ab35675fb9c950d9083d44d47bad1e538cf77e2a303924`,
and independently compiled it on the pinned Lean 4.33.1 runtime. All eleven
reported declarations passed kernel assertions and their transitive axiom
lists contain only propext, Classical.choice, and Quot.sound.

The proof uses actual matrix singular values, sorted self-adjoint eigenvalues,
and the characteristic-polynomial coefficient identity for the literal sum
of principal minors. Row restriction decreases each retained singular value.
The small-singular subspace has dimension at least r; inverse-Gram quadratic
forms on it are bounded below by t^-2 using the positive-definite Cauchy
inequality. Courant--Fischer then bounds the rth largest inverse-Gram
eigenvalue. All eigenvalues are positive, so the selected product and finite
averaging yield an actual subset of size r with principal determinant at
least t^(-2r)/choose(m,r). The guards 1<=r<=m<=n and t>0 ensure the stated
index m-r and denominator are valid. No spectral estimate is assumed.

Approved exact statement and proof. The separate Gaussian probability
assembly and the complete IE-06 conclusion require their own checks.
