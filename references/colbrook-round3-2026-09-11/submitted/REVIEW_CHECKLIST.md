# Independent mathematical review checklist

These are suggested checks, not a record that an independent review has occurred.

## IE-10

- Confirm that the complex-sphere start becomes independent exponential weights up to common normalization, without replacing the Krylov space by an independent random subspace.
- Check that Jf(zeta_j) = zeta_j^(k-1) conjugate(f(zeta_j)) preserves the polynomial subspace and satisfies JHJ = H*. This gives equal coordinate magnitudes for a matched left/right eigenpair.
- Check the generalized-eigenvalue derivative, including the derivative of the Gram matrix. Verify the exact identity (6) and the reverse-triangle argument in Lemma 2.
- Check the balanced column scaling in Lemma 3. This controls the infimum of eigenbasis condition numbers, not just an arbitrary numerical eigenvector normalization.
- Verify generic simplicity from a boundary-weight specialization, and almost-sure nonvanishing of each conditional discriminant polynomial. The restriction k < n is used to keep G_0 positive definite.
- For the independent proof, check the discriminant degree, exceptional-coordinate probability, invertibility for Re(t) > 0, holomorphic root labels, Cauchy's derivative estimate, and both union/Markov bounds.
- For the sharper proof, check the crossing count with multiplicities in Lemma 5. A moving root determines a unique parameter; common roots are constant branches. Coordinate variation, not merely the image of a curve, is being bounded.
- Check Tonelli conditioning, the use of t exp(-t) <= 1, cyclic separation d >= 4/n, and the constants 1700 and 3. The all-k corollary does not assume independent compressions.

## IS-04 explicit-family partial result

- Confirm that every kernel entry is a sign, including the origin and flip locations, and that the matrix class matches unrestricted real sign matrices.
- Verify the exact cardinality of the flip set and the exact zero-frequency correction to epsilon times p.
- Check the Gauss-transform sign convention and the anisotropy of both quadratic forms.
- Verify the classical mixed Weil bound, including its constant 2 and the nontrivial-ramification hypotheses. The manuscript gives precise primary-source locators for the imported input.
- Check the convolution diagonalization and convert eigenvalue moduli to singular values using normality.
- Check the positivity threshold, asymptotic rate, and exact comparison 210^2 < 2*151^2.
- Keep the quantifiers separate: n = p^2 is an infinite subsequence. This does not prove the every-dimension upper bound in IS-04. The additional full claim is about Problem 13 of the source paper, not another repository entry.
