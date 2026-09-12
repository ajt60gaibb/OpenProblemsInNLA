# Self-review — SP-08

**Highest-priority audit:** Theorem 1 (signed-threshold reduction). Exact
certificates cannot repair a mistake connecting the finite family to the
continuous box. Check the perturbation argument, diagonal sign entries,
simultaneous permutation and global sign normalization d_1=1.

The implementation was inspected and all three full verifications were rerun:
32,768; 524,288; and 2,097,152 patterns, with 5,648; 65,077; and 222,013 distinct
polynomials. The logs are under `verification/recheck_n*.log`. Coverage compares
actual polynomial sets. Every rational certificate is validated with arbitrary
precision integers, and rank-two equality certificates have an exact negative
quadratic constant term. The n=8 second representative-polynomial checker and
a separately implemented Taylor-coefficient certificate checker are included
for additional diagnostics; consult their execution logs for actual runs.

Checked: closed interval endpoints, free diagonal entries, real symmetry,
rank exactly two of the explicit attainers, negative and positive nonzero
eigenvalues, zero middle eigenvalues, exact rescaling by two, and all entries of
both coefficient-sign certificates. The checked overflow bound is smaller than
2^63 before NumPy int64 arithmetic is used; arbitrary-precision arithmetic is
used for the rational-root certificates.

Floating-point eigensolvers are used only in the *generation* routine to suggest
bounds. The proof-verification routine calls no eigensolver. The independent
Taylor-coefficient checker does not regenerate coverage and is labeled
accordingly. No amount of finite certification establishes the all-n conjecture.

This is self-review, not independent agent review, formal proof-assistant
verification, or a novelty determination. Recommendation: retain PARTIAL.
