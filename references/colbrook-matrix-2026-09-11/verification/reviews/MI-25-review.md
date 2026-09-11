# MI-25 independent proof review

**Verdict: PASS for the expressly endpoint-only theorem — C_1 is infinite, already on real 2-by-3 matrices. The full Schatten-scale canonical problem remains partially resolved.**

Review date: 2026-09-11. Reviewer: independent agent `/root/review_matrix_orbits`. Canonical target: `matrix-inequalities-and-norms/MI-25/README.md`. Original read in full: `.cache/colbrook-matrix-submission/nla_submission/proofs/MI-25-endpoint.tex`; the bundle preamble and bibliography were also read.

## Full original identity

SHA-256: `4926b803e07c3b3184ef6225aeddb2bf0821a696e1150d4e94567027b20f889e`.

Hash procedure: decode the entire original file as strict UTF-8, replace CRLF by LF, re-encode as UTF-8, and hash, with no extraction, trimming, or other whitespace changes. Original and normalized lengths are both 2,787 bytes; no bare CR occurs. This review attaches to that full TeX identity, not to an extracted proof or independently rendered PDF.

## Target and source alignment

Canonical C_p is uniform over all complex rectangular dimensions and triples. At p=1 the norm is the sum of singular values. The three-summand defect N and sum D of all three pairwise defects match equation (48), including its multiplicities. The source explicitly asks for Schatten constants and leaves the trace-norm constant's finiteness unsettled; its numerical observation is motivation, not part of this proof. [Audenaert–Kittaneh, arXiv v3, Problem 7, equation (48), and following discussion](https://arxiv.org/html/1201.5232v3#S8.SS2).

## Complete proof audit

1. The three displayed vectors u_j are real unit vectors separated by 120 degrees. Direct outer-product addition gives sum_j u_j=0 and sum_j u_j u_j^T=3I/2, and their pairwise inner products are -1/2. For 0<t<1, v_j=(sqrt(1-t)u_j,sqrt(t)) has squared norm one. Therefore X_j=u_j v_j^T is a real 2-by-3 rank-one matrix with singular values 1 and 0, and trace norm one. The rectangular dimensions are within the canonical quantifier.

2. Summing the two-column portion of X_j gives sqrt(1-t) times sum u_j u_j^T, while the third column is sqrt(t) sum u_j=0. Hence the sum has two equal singular values (3/2)sqrt(1-t), trace norm 3sqrt(1-t), and defect N=3(1-sqrt(1-t)).

3. For each pair, set U=(u_i,u_j), a 2-by-2 matrix, and V=(v_i,v_j), a 3-by-2 matrix. Both have full column rank for the open interval in question. The Gram matrices have the printed off-diagonal entries -1/2 and (3t-1)/2, respectively. The squared singular values of UV^T are the eigenvalues of the positive matrix (U^T U)^(1/2)(V^T V)(U^T U)^(1/2): this follows from the polar factorization of the invertible U, or the equality of nonzero product eigenvalues. Because the two Gram matrices commute and share eigenvectors (1,1) and (1,-1), these values are their paired eigenvalue products (1+3t)/4 and 9(1-t)/4. Thus the pair trace norm q(t) is exactly the sum of their positive square roots as stated. No assertion that a nonsymmetric Gram product is automatically positive is needed.

4. Every pair has the same trace norm, so D=3(2-q(t)). Cancelling the common factor three gives the manuscript's defect ratio. Strict concavity of sqrt with weights 1/4 and 3/4 applies to distinct positive arguments 1+3t and 1-t, whose weighted mean is one. It gives q(t)/2<1 for every 0<t<1. Hence D>0 on the entire family and division is legitimate. The canonical requirement to include triples with D=0 is not evaded: an unbounded ratio on admissible positive-D triples alone excludes every finite universal constant.

5. The Taylor coefficients check independently: sqrt(1-t)=1-t/2-t²/8+O(t³), and q(t)=2-3t²/4+O(t³). Thus N/D is asymptotic to 2/(3t). The alternative exact argument also checks. With g=sqrt((1-t)(1+3t)), direct squaring gives q²=5/2-3t/2+3g/2, so 4-q²=(3/2)(1+t-g). Moreover (1+t)²-g²=4t². Rationalizing twice yields 2-q=6t²/((1+t+g)(2+q)), precisely as printed. Dividing the rationalization 1-sqrt(1-t)=t/(1+sqrt(1-t)) by this expression reproduces the exact ratio and its divergence. All denominators are positive for 0<t<1. No numerical extrapolation is used.

6. Appending one zero row to each matrix preserves its right Gram matrix and hence every singular value. It does so for every individual, pair, and triple sum. Thus the same defects and unbounded ratio occur in real square 3-by-3 matrices. This confirms that the failure is already at fixed dimensions, stronger than mere failure along dimensions tending to infinity.

## What remains and review limits

The theorem establishes C_1=infinity in the canonical convention that no finite constant works. It makes no assertion of a meaningful product infinity times zero. It supplies no determination of C_p for 1<p<infinity; the already-known p=2 value C_2=1 is not altered or reproved. Therefore the whole MI-25 entry must retain partial status, with the trace endpoint recorded separately from the remaining Schatten exponents. The operator-norm endpoint p=infinity is outside the canonical finite-p range and is not a consequence needed here. No material gap was found. This is independent agent review, not external human peer review, formal verification, or an exhaustive novelty/priority search. No canonical or original proof edits were made.
