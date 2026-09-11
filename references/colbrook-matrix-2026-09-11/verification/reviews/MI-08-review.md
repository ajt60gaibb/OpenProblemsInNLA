# MI-08 independent proof review

**Verdict: PASS for the expressly partial theorem — fixed and adaptive lengths equal the partial-Hadamard column length, and the exact length is 12 in dimensions 9 through 12. The all-dimension canonical optimization remains unresolved.**

Review date: 2026-09-11. Reviewer: independent agent `/root/review_matrix_orbits`. Canonical target: `matrix-inequalities-and-norms/MI-08/README.md`. Original read in full: `.cache/colbrook-matrix-submission/nla_submission/proofs/MI-08-partial.tex`; the bundle preamble and bibliography were also read.

## Full original identity

SHA-256: `8ca9b6e9a869d665b689c9c5a60912bda1b4fe9116a4c48c65f8645b2bc4355b`.

Hash procedure: decode the entire original file as strict UTF-8, replace CRLF by LF, re-encode as UTF-8, and hash, with no extraction, trimming, or other whitespace changes. Original and normalized lengths are both 3,633 bytes; no bare CR occurs. This review attaches to that full TeX identity, not to an extracted proof or independently rendered PDF.

## Target and source alignment

Canonical phi(d) is the fixed-list length f(d), with the same equal-weight orthogonal conjugations working for every real d-by-d matrix. Adaptive a(d) instead permits the conjugations to depend on that matrix while retaining a uniform length. Both quantifier orders match the source's adjacent Questions 4.8 and 4.9. Those questions include nonsymmetric real matrices; the adversarial input D+K is therefore admissible. [Bourin–Lee, arXiv v2, Questions 4.8–4.9](https://arxiv.org/html/2606.15624v2#S4).

## Complete proof audit

1. If H is a q-by-d sign matrix with H^T H=qI, its rows define q real diagonal orthogonal matrices. On entry (j,l), their average conjugation multiplies x_jl by q^(-1) sum_i h_ij h_il, which is one for j=l and zero otherwise. Thus one list works for every real input and a(d)≤f(d)≤h(d). Sylvester sign matrices give a finite admissible q for every positive d; the minima exist over positive integers.

2. Choose D=diag(1,...,d) and the displayed real skew-symmetric K, with every off-diagonal entry nonzero. For any representation of Delta(D+K)=D by q orthogonal conjugations, taking the symmetric part removes K and gives sum_i O_i D O_i^T=qD. Frobenius norms are unchanged by orthogonal conjugation. Expanding their squared distances from D gives exactly 2q||D||_F² minus 2 tr(D sum_i O_i D O_i^T)=0. Each squared distance is nonnegative, so each is zero. This uses equality in a strictly convex Euclidean norm in a fully explicit form.

3. Thus O_i D O_i^T=D, and multiplication on the right by O_i yields O_i D=D O_i. Since D has simple diagonal entries, its entrywise commutation equations force every off-diagonal entry of O_i to vanish. Orthogonality makes its diagonal entries signs. Taking skew-symmetric parts of the original representation now yields sum_i (O_i)_jj (O_i)_ll=0 for each j≠l, since k_jl is nonzero. The resulting q-by-d sign matrix has orthogonal columns and column squared norms q. Therefore every adaptive representation of this one input has q≥h(d); a(d)≥h(d). The argument also covers d=1, with the off-diagonal condition vacuous. Together these steps prove f(d)=a(d)=h(d) for all positive d.

4. Rank gives q≥d. For d≥3, multiply rows by the first-column signs, preserving column orthogonality and making the first column all ones. Orthogonality of columns two and three to column one makes each balanced. If their four sign-pair counts are n_++,n_+-,n_-+,n_--, their two balance equations, mutual orthogonality, and total count q solve to n_++=n_+-=n_-+=n_--=q/4. Hence 4 divides q. This establishes q≥12 throughout 9≤d≤12.

5. The order-twelve construction is valid. The nonzero squares modulo 11 are exactly {1,3,4,5,9}, so chi(-1)=-1, Q^T=-Q, and Q1=0. Here is an independent algebraic verification of the submitted identity QQ^T=11I-J, without using the accompanying verifier. Its diagonal entries are ten. For distinct row indices, substitution and rescaling reduce the row dot product to S=sum_x chi(x(x+1)). Count solutions y²=x(x+1) over F_11: their number is 11+S. The invertible transformation r=2x+1-2y, s=2x+1+2y converts that equation into rs=1. There are ten choices of nonzero r and a unique s=r^(-1), each recovering a unique x,y because two and four are invertible. Hence 11+S=10 and S=-1. This proves every off-diagonal entry is -1.

6. The entries of H are all signs: Q has zero diagonal so Q-I has diagonal -1 and off-diagonal signs. Its upper-left Gram entry is 12 and its off-diagonal Gram blocks vanish because Q1=0 and the row sums of Q-I are -1. Its lower-right Gram block is J+(Q-I)(Q^T-I)=J+QQ^T+I=12I, using Q+Q^T=0. Thus HH^T=12I. Since H is square and invertible, also H^T H=12I; choosing any d columns gives the required upper bound h(d)≤12. Combined with the lower bound, the claimed exact dimensions follow.

## What remains and review limits

The equality phi(d)=h(d) is a rigorous reformulation, not an explicit determination of h(d) in all dimensions. In particular, h(4m)=4m holds exactly when there exists a Hadamard matrix of that order: a square sign matrix with orthogonal columns is precisely such a matrix. The proof neither constructs these at all orders nor decides all possible rectangular sign-column counts. Consequently MI-08 must retain partial status. The value phi(9)=12 does refute a universal choice between 9 and its next power of two, 16. The adaptive conclusion concerns all real inputs and must not be advertised for a restriction to symmetric inputs. No material gap was found in the submitted partial result. This is independent agent review, not external human peer review, formal verification, or an exhaustive novelty/priority search. No canonical or original proof edits were made.
