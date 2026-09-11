# MI-23 independent proof review

**Verdict: PASS — complete negative resolution of the exact corrected canonical conjecture.**

Review date: 11 September 2026. Reviewer: separate agent `/root/review_matrix_exact`. Read the full original `.cache/colbrook-matrix-submission/nla_submission/proofs/MI-23.tex`, preamble, relevant references, and `matrix-inequalities-and-norms/MI-23/README.md`. No proof or canonical edits were made.

## Exact original identity

SHA-256 for the full original TeX decoded UTF-8, normalized to LF, and re-encoded without trimming: `1556c3d537ef73392fb61be9fd5a41a401fa3c6b1fab5bba4ba0c37fc413f37f`. Original and normalized byte lengths: 2,623; no bare CR. This review applies to that entire section including its remark, not just the proof environment.

## Target and primary source

The canonical generalized mean G_{r,t} is identical to the manuscript's A#_{r,t}B, including A^(r/2) on both outer sides. The target uses eigenvalues of products of powered means, not singular values of unpowered means, and compares against A^(p(r+s-1))B^p. Parameters r = s = 1, p = 2, t = 1/8 satisfy the conjecture's inclusive ranges. A single violation of the first ordered eigenvalue inequality refutes log-majorization in dimension three.

Independently checked the actual replacement [Conjecture 2.1 and equation (13), printed p. 6](https://arxiv.org/pdf/2105.13356). Its full t interval is [0,1]; the established p = 2 interval for r = s = 1 is [1/4,3/4]. The submitted point lies outside that proved region. The example addresses the corrected eigenvalue conjecture, not only the earlier refuted singular-value formulation.

## Positive definiteness and powers

The leading principal minors of the real symmetric T are exactly 2, 49, and 150, as independently recomputed. Sylvester's criterion therefore establishes T > 0. D is positive diagonal and invertible, so A = D^2 > 0 and B = DT^8D > 0 by congruence. A^(1/2) = D. Thus A^(-1/2)BA^(-1/2) = T^8. Because T is PD, its spectral eighth power has unique positive eighth root T. It follows that its powers 1/8 and 7/8 equal T and T^7, exactly. Both means G = DTD and H = DT^7D are PD rational matrices.

## Correct eigenvalue reduction

H(G^2H^2)H^(-1) = HG^2H = (GH)^*(GH). Thus the largest eigenvalue of G^2H^2 is the square of the operator norm of GH. The same conjugation argument with B gives lambda_max(A^2B^2) = ||AB||_op^2. All similarity matrices are invertible and all spectra are positive. This is a legitimate reduction of the requested eigenvalue inequality even though the products themselves need not be Hermitian.

## Every exact numerical certificate

Using independently written standard-library rational matrix multiplication and no supplied verification code, I reconstructed T^7, T^8, A, B, G, H, and the products. The results are:

\[
(GH)_{13}=1260589125202/9>140000000000,
\]

\[
\|AB\|_F^2=2009446159144992718181231562721/107495424
<(138000000000)^2,
\]

and

\[
((GH)_{13})^2-\|AB\|_F^2
=99434824489435745411095588895/107495424>0.
\]

All displayed values and both integer thresholds agree with exact recomputation. The standard bounds |e_1^*GH e_3| <= ||GH||_op and ||AB||_op <= ||AB||_F, combined with the strict certificate, prove ||GH||_op > ||AB||_op. Both sides are nonnegative, so squaring preserves this strict reversal. The largest-eigenvalue inequality therefore fails. As a supplementary consistency check, exact determinants satisfy det(G^2)det(H^2) = det(A^2)det(B^2), in accord with the total-product equality required by the intended log-majorization.

## Review limits

No material gap was found. The counterexample disproves the full universal conjecture; it neither classifies all remaining parameter points nor contradicts the narrower proved interval. Exact arithmetic removes any dependence on condition numbers or fractional-power numerical accuracy. The separate script `independent_exact_counterexamples.py` is supplemental reproducibility evidence, not a formal proof checker. This is an independent agent audit, not external human peer review, and does not certify novelty or exhaustively search later literature.
