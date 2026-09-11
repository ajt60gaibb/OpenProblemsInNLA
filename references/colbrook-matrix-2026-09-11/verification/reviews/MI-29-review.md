# MI-29 independent proof review

**Verdict: PASS — complete negative resolution of the arbitrary-exponent Hermitian-input extension.**

Review date: 11 September 2026. Reviewer: independent agent `/root/review_matrix_exact`. Read the full original `.cache/colbrook-matrix-submission/nla_submission/proofs/MI-29.tex`, preamble, relevant bibliography, and `matrix-inequalities-and-norms/MI-29/README.md`. No proof or canonical statement was edited.

## Full original identity

Full-file SHA-256 after UTF-8 decoding and normalization to LF with no trimming: `90973535fd44eac8f45f5016b10c1bf05d61d90e3917054102abdb517cab8584`. Original and normalized byte lengths: 2,268; no bare CR. The identity covers the complete section, proof, and hypothesis-distinction remark. PASS applies to that full original and the canonical target read today.

## Precise target and primary-source distinction

The target is det(A^k + |AB|^p) >= det(A^k + |BA|^p) for every PD A, invertible Hermitian B, and k,p >= 0. The example uses dimension three, k = 6, p = 8. It does not concern only the established k = 2 theorem, and the target does not require B >= 0.

I independently accessed the author's uploaded thesis. Its final Open Problems, Problem 2, explicitly states A positive semidefinite, B Hermitian, and all k,p >= 0, with exactly this modulus order. Its subsequent status note singles out k = 2 and further cases under A,B >= 0. Thus the repository's invertible/PD formulation is a subcase of the actual arbitrary-exponent question, not a mistaken extrapolation of a theorem. See [Ghabries thesis, final Problem 2, pp. 109–110](https://www.researchgate.net/publication/361793582_Contributions_to_Matrix_Inequalities_and_Some_Applications).

The squared-base scope is also confirmed by [the 2026 paper, §3, Theorem 3.4 and Remark 3.1](https://arxiv.org/html/2607.21163). The 2020 DOI endpoint did not return usable full text in this audit; the thesis and 2026 primary text provided the independently checked scope evidence. This limitation does not enter the self-contained counterexample.

## Hypotheses and correct modulus orientation

A = diag(2,1,1/2) is PD. The displayed real symmetric B has det B = -1/125, as recomputed directly, and is invertible. Its quadratic forms on e_1 and e_2 have opposite signs (-1/5 and 1/5), so it is indefinite, exactly as the remark states. Indefiniteness is allowed.

For these self-adjoint inputs, |AB|^2 = (AB)^*(AB) = BA^2B, whereas |BA|^2 = AB^2A. Both are PD because the products are invertible. With M = 5B, raising these squared moduli to the fourth power gives |AB|^8 = 5^(-8)(MA^2M)^4 and |BA|^8 = 5^(-8)(AM^2A)^4. Thus H belongs on the conjectured left and J on its right. No modulus reversal or fractional-power convention is being assumed. D = A^6 is PD, so both determinant arguments are PD and their determinants are positive.

## Exact polynomial and determinant certificates

For 3 by 3 matrices, determinant multilinearity yields

\[
\det(D+zK)=\det D+z\operatorname{tr}(\operatorname{adj}(D)K)
+z^2\operatorname{tr}(\operatorname{adj}(K)D)+z^3\det K.
\]

The constant terms cancel in the difference. Also det H = det J: each equals (det M)^8(det A)^8 (here both determinants before the eighth powers have absolute value one). Hence the cubic terms cancel. Independently multiplying the rational matrices and expanding the determinant through the six signed permutations, selecting D or zK in each factor, gives

\[
\det(D+zJ)-\det(D+zH)
=\frac{2089017}{16}z-\frac{31188746592549}{1024}z^2.
\]

This computation does not reuse the manuscript's adjugate formula or its supplied verifier. All four coefficients, including the zero constant and cubic coefficients, were asserted exactly.

Direct determinant evaluation at z = 1/390625, independently of polynomial evaluation, gives

\[
\det(A^6+|AB|^8)=136990346414301954149/61035156250000000000,
\]

\[
\det(A^6+|BA|^8)=4537743716162890657/1907348632812500000.
\]

Their difference (right minus left) is exactly 21036678407451/156250000000000 > 0. These are precisely the submitted individual determinants and strict gap. The sign contradicts the conjectured direction, establishing a counterexample with every canonical hypothesis satisfied.

## Limits

No material mathematical gap was found. This is a negative answer to the full arbitrary-k Hermitian-input universal statement. It does not refute the known k = 2 theorem, settle all parameter slices, or settle the variant B > 0. No singular limit or zeroth-power convention is needed. The audit checks source scope and the full rational proof, but not exhaustive literature priority or novelty. This is independent agent review, not external human peer review or formal proof verification. Reproducible supplemental arithmetic is retained in `independent_exact_counterexamples.py`.
