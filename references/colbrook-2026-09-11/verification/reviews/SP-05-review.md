# Independent agent proof review: SP-05

- **Verdict: PASS.** The entire displayed SP-05 target follows from the reviewed proof; the stronger assertion of a nonzero real positive-semidefinite minimizing eigenmatrix is also established.
- **Review date:** 11 September 2026.
- **Reviewer:** independent verification agent `/root/review_sp05_ke04`.
- **Target read:** [SP-05/README.md](../../../../eigenvalues-and-inverse-problems/SP-05/README.md), specifically its complete problem statement.
- **Proof read:** [SP-05/solution.md](../../../../eigenvalues-and-inverse-problems/SP-05/solution.md), Theorem SP-05 and sections 1–3.
- **Proof SHA-256:** `54ef24c91eb717efca2c3a04fdbbbcba91485e214984c45245904aba55209f42`.
- **Hash convention:** UTF-8 bytes of the substring beginning at `## Theorem ` and ending immediately before `## Scope and review notes`, after replacing CRLF and CR with LF and stripping leading/trailing whitespace. The resulting block has 3483 bytes.

## Exact scope and method

The target asks whether, for every pair of real symmetric positive definite matrices A and B of size n at least two, the minimum Rayleigh quotient of A tensor B on vectors fixed by transposition is at most its minimum on vectors negated by transposition. The proof asserts the stronger result that the smallest eigenvalue of L(X) = AXB + BXA has a nonzero real positive-semidefinite eigenmatrix. I independently checked every implication from the hypotheses to that stronger assertion and then to the exact sector inequality. I used the local target and proof, not the supporting diagnostics, previous status checks, or a presumption that the claim was correct.

This review concerns the mathematics in the hashed block. It does not certify literature completeness, novelty, publication, author metadata, or consistency of separately generated PDF/LaTeX artifacts.

## Checked derivations

### 1. Operator properties on the required spaces

On complex matrices with Frobenius inner product, the map X to AXB is self-adjoint because A and B are Hermitian: cyclicity of trace gives `<X, AYB> = <AXB, Y>`. The same holds for X to BXA. Furthermore,

`<X, AXB> = tr(X* A X B) = ||A^(1/2) X B^(1/2)||_F^2`.

The square-root factors are invertible, so this is strictly positive for nonzero X. Thus L is positive definite and self-adjoint on the full complex matrix space and on its real subspace. In particular, L is invertible, every eigenvalue is positive, and its inverse Phi is self-adjoint and positive definite. The real coefficients give a real representation of both operators. Direct transposition yields `L(X)^T = L(X^T)`; invertibility transfers this commutation relation to Phi.

Under column vectorization, AXB corresponds to B tensor A, and BXA to A tensor B. Their sum is exactly the matrix stated in the target; the order of the two summands has no effect.

### 2. Inverse congruence and integral

Substitute `X = B^(-1/2) Xtilde B^(-1/2)` into L(X) = Y and multiply on the left and right by B^(-1/2). The first term becomes `C Xtilde` and the second becomes `Xtilde C`, with `C = B^(-1/2) A B^(-1/2)`. This verifies the congruence reduction without requiring A and B to commute.

C is real symmetric positive definite. If its smallest eigenvalue is c > 0, then `||exp(-tC)||_2 <= exp(-ct)`, which gives absolute convergence of the proposed integral. Differentiating `exp(-tC) Ytilde exp(-tC)` and integrating from zero to infinity gives exactly `C Xtilde + Xtilde C = Ytilde`; the boundary term at infinity vanishes. The Sylvester map is invertible since its eigenvalues in an eigenbasis of C are the positive numbers c_i + c_j. Thus the integral is the unique inverse, not just a possible solution.

Substituting the two congruences back gives

`Phi(Y) = integral_0^infinity M_t Y M_t dt`,

where `M_t = B^(-1/2) exp(-tC) B^(-1/2)` is real symmetric. This expression has the correct factors on both sides of Y. For any complex Hermitian Y >= 0 and any complex vector z,

`z* M_t Y M_t z = (M_t z)* Y (M_t z) >= 0`.

Therefore each integrand, and the convergent integral, is complex Hermitian positive semidefinite. Positivity on the complex Hermitian cone is proved explicitly; it is not inferred solely from positivity on real symmetric inputs.

### 3. A Hermitian top eigenmatrix

Let r be the largest eigenvalue of Phi. Its real symmetric matrix representation supplies a nonzero real eigenmatrix Z for r. Since Phi commutes with transposition, both `(Z + Z^T)/2` and `(Z - Z^T)/2` satisfy the same eigenvalue equation; at least one is nonzero. Hence the choice of a nonzero symmetric or skew-symmetric W is justified, including when the eigenspace has dimension greater than one.

For symmetric W, H = W is Hermitian. For real skew-symmetric W, `(iW)* = iW`, so H = iW is Hermitian. Complex linearity ensures Phi(H) = rH also in the latter case. There is no assumption that the top eigenmatrix was initially symmetric.

### 4. Modulus comparison and realness

The Hermitian spectral decomposition supplies H = H_+ - H_- with H_+, H_- positive semidefinite and H_+ H_- = 0. Expanding both quadratic forms gives a difference of twice the sum of the two cross terms. Self-adjointness makes the cross terms equal, and their Hermitian form makes them real. This gives exactly

`<|H|, Phi(|H|)> - <H, Phi(H)> = 4 tr(H_+ Phi(H_-)) >= 0`.

The last sign follows from the proved cone preservation and the identity `tr(PQ) = tr(P^(1/2) Q P^(1/2)) >= 0` for Hermitian P,Q >= 0. Commutativity of P and Q is unnecessary. Orthogonality of the positive and negative spectral parts gives `|||H|||_F = ||H||_F`.

If W is real symmetric, its modulus is real symmetric by its real orthogonal diagonalization. If W is real skew-symmetric, `H^2 = -W^2 = W^T W` is real symmetric positive semidefinite. Its unique positive-semidefinite square root is real symmetric, so `|H| = sqrt(H^2) = sqrt(-W^2)` is real in this case as well. This also covers singular W, zero eigenvalues, and odd n. Nonzero H implies nonzero |H|.

### 5. Variational conclusion

The quadratic form of H equals `r ||H||_F^2`. The modulus comparison and equal norms show that |H| has Rayleigh quotient at least r. The largest-eigenvalue variational bound for the self-adjoint Phi supplies the opposite inequality. Equality implies that |H| lies in the r-eigenspace: in an orthonormal eigenbasis, every squared component with eigenvalue strictly below r must vanish. This conclusion holds with arbitrary eigenvalue multiplicity.

As L is positive definite, the eigenvalues of Phi are the positive reciprocals of those of L. Therefore `1/r = lambda_min(L)`, and `L(|H|) = (1/r)|H|` proves the stronger real positive-semidefinite assertion.

### 6. Exact symmetric/skew-symmetric inequality

The commutation matrix T is a real orthogonal symmetric involution. For K = A tensor B, the identity `T K T = B tensor A` follows either from vectorization or from swapping the tensor factors. If Tv = epsilon v with epsilon equal to +1 or -1, then

`v^T (K + TKT) v = 2 v^T K v`.

The sum commutes with T, so both transpose sectors are invariant. The nonzero minimizing eigenmatrix already constructed belongs to the symmetric sector. Hence the symmetric-sector minimum for the sum equals its global minimum and is no greater than its skew-sector minimum. Dividing the sector Rayleigh quotients by two gives exactly the displayed target inequality for A tensor B. For n >= 2 both sectors contain nonzero vectors, so both minima in that target are defined and attained.

## Gap search and boundary cases

No mathematical gap was found. In particular, the argument does not silently assume that A and B commute, that the inverse preserves entrywise positivity, that a top eigenmatrix is symmetric, that W is invertible, or that the extremal eigenvalue is simple. Cases H_+ = 0 or H_- = 0 cause no difficulty in the cross-term identity. Repeated eigenvalues of A, B, C, or Phi are harmless. The theorem's stronger assertion also makes sense for n = 1, though the target restricts n >= 2 so that the skew sector is nonempty. Singular positive-semidefinite or indefinite input matrices are outside the hypotheses and are not certified by this review.

## Review limits

PASS means that this independent agent audit verified the full target from the supplied proof and found no gap. It is an agent review, not external human peer review, a formal proof certificate, or an assertion of mathematical priority. No manuscript, catalog status, code, or remote file was changed by this reviewer.
