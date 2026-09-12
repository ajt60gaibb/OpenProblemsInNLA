# MI-22 independent proof review

**Verdict: PASS — certified counterexample to the full canonical universal assertion.** Every finite certificate was independently recomputed using exact rational arithmetic, and the analytic bridge to the true matrix roots was separately checked.

Reviewed 2026-09-11. Original: `.cache/colbrook-matrix-submission/nla_submission/proofs/MI-22.tex`. SHA256 of the complete original decoded as UTF-8, replacing CRLF by LF, with no trimming: `4c7c612af0a3f285c1d373d16847450d7fb99582fd2906eec8202c2a8ea9c5a4`.

## Exact target and source check

The canonical `matrix-inequalities-and-norms/MI-22/README.md` asks for singular-value log-majorization of A^t(A#_t B)B^(1-t) by AB for all positive definite A,B and 0<=t<=1. The manuscript uses exactly the canonical weighted mean and matrix order. A failure of the k=1 inequality in dimension three refutes the universal assertion, regardless of determinant equality or the behavior of other partial products.

The [primary Ghabries–Abbas–Mourad–Assi preprint](https://arxiv.org/pdf/2105.13356), printed pages 2–3, defines the same mean, descending singular values and log-majorization, and states the target as Conjecture 1.1. Its semidefinite domain includes the positive definite inputs here. Conjecture 1.2 and the eigenvalue-modulus result in Theorem 3.2 are different assertions. This review checked the original target, not the later literature's novelty/open-status claims. The shared preamble's operator-norm convention was checked.

## Independent exact computation

The reviewer wrote [MI-22-independent-check.py](MI-22-independent-check.py), using Python standard-library `fractions.Fraction`, permutation-expansion determinants, and sequential matrix multiplication. It does not import the submitted verifier or its linear-algebra routines. The R and S entries are parsed directly from the full original TeX, which binds the recomputation to the reviewed proof rather than to a potentially inconsistent duplicate certificate. A,B are independently transcribed and C is computed by congruence and compared with the displayed value.

The script completed with PASS under the bundled Python runtime. [MI-22-independent-check.json](MI-22-independent-check.json) records the complete exact leading minors, squared residual fractions, rational left entry, error bound, norm bound and normalized original hashes. Every asserted strict rational comparison passed. In particular:

- B's leading principal minors are 17, 278529, 4096; A has strictly positive diagonal entries.
- Both B-2^(-10)I and C-2^(-10)I have all three leading minors positive.
- R-9I/20, 8I-R, S-9I/20 and 4I-S are symmetric and each has positive leading minors. Sylvester's criterion is applicable.
- The exact sums of squares of the nine entries of R^8-C and S^8-B are each strictly below 10^(-16).
- (9/20)^8>2^(-10); trace(C)<8^8 and trace(B)<4^8.
- The exact (1,2) entry of diag(32,1/32,1) R diag(16,1/16,1) S^7 exceeds 11000.
- The propagated error is exactly 6291456/78125<100.
- ||AB||_F^2 is exactly 6807858741265/65536<10200^2.

The supplied `exact_linear.py`, `verify.py` MI-22 routine and duplicate certificate were also read. Their checking strategy agrees with the mathematics, but the independent result above is the finite-certificate evidence used for this review. No floating-point eigensolver, residual estimate, singular value, or printed decimal is trusted.

## Analytic audit

1. **Root Lipschitz lemma:** the scalar fractional-power integral is valid for 0<alpha<1 and positive operators. Subtracting its two spectral-calculus forms and applying the resolvent identity gives the displayed order of resolvents and P-Q. Each resolvent norm is at most 1/(u+m). The integrable dominating scalar is u^alpha/(u+m)^2; the integral converges at both endpoints. Differentiation of the scalar formula at m gives alpha m^(alpha-1). This proves an operator-norm estimate for noncommuting P,Q and does not assume scalar Lipschitz continuity implies operator Lipschitz continuity.

2. **Identifying the true roots:** C=A^(-1/2)BA^(-1/2)>0. X=C^(1/8) and Y=B^(1/8) are their positive principal roots. Since R,S>9I/20, spectral calculus gives R^8,S^8>(9/20)^8 I>2^(-10)I, and the positive eighth root of R^8 is R (likewise S). Thus the lemma applies to (C,R^8) and (B,S^8), with all its hypotheses certified.

3. **Residual to root error:** the Frobenius-square inequalities yield operator residuals below 10^(-8). The Lipschitz coefficient is (1/8)(2^(-10))^(-7/8)=2^(23/4)<64. Therefore both root errors are strictly below epsilon=64*10^(-8). Positivity and the trace bounds give ||X||<8 and ||Y||<4 independently of their approximations.

4. **Product order:** expanding the weighted geometric mean gives L=A^(5/8) X A^(1/2) Y^7. The two diagonal powers of A are exactly those displayed. This does not commute X through any other factor. The telescoping identity for Y^7-S^7 has seven ordered products, valid even when Y and S do not commute. Each term is bounded by 4^6 epsilon.

5. **Error propagation:** split L-Ltilde into A^(5/8)(X-R)A^(1/2)Y^7 and A^(5/8)R A^(1/2)(Y^7-S^7). Submultiplicativity and the certified upper bounds give precisely 32*16*epsilon*(4^7+8*7*4^6), the independently checked rational value below 100.

6. **Strict contradiction:** a matrix entry is bounded in modulus by the operator norm, and |L_12-Ltilde_12|<=||L-Ltilde||<100. Since Ltilde_12>11000, ||L||>10900. Conversely ||AB||<=||AB||_F<10200. The strict separation therefore concerns the actual principal matrix powers and disproves s_1(L)<=s_1(AB). All inputs are real symmetric positive definite, n=3 and t=1/8 is in the allowed interval.

## Limitations and disposition

No material gap was found. This is a rigorous computer-assisted counterexample, with exact finite calculations plus a checked analytic error bound. The program is not a formal verification kernel; correctness still rests on elementary arithmetic/linear-algebra reasoning and the reviewed Python operations. The proof does not classify all parameter ranges or all valid weaker statements, and does not need to do so to refute this conjecture. It supports a negative resolution of the canonical universal MI-22 target. Original proof and canonical files were not edited by this reviewer.
