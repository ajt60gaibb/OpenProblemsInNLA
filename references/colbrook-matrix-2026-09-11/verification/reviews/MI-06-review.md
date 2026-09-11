# MI-06 independent proof review

**Verdict: PASS — complete negative resolution of the exact canonical target, with the stronger failure of every finite constant in dimension three.**

Review date: 2026-09-11. Reviewer: independent agent `/root/review_matrix_orbits`. Canonical target: `matrix-inequalities-and-norms/MI-06/README.md`. Original read in full: `.cache/colbrook-matrix-submission/nla_submission/proofs/MI-06.tex`; the bundle preamble and bibliography were also read.

## Full original identity

SHA-256: `1324c6ecd4a845e6782081e79d401a9dd59612463e40b7ecc176a9ea9003c1e9`.

Hash procedure: decode the entire original file as strict UTF-8, replace CRLF by LF, re-encode as UTF-8, and hash, with no extraction, trimming, or other whitespace changes. Original and normalized lengths are both 3,003 bytes; no bare CR occurs. This review attaches to that full TeX identity, not to an extracted proof or independently rendered PDF.

## Target and source alignment

The target uses the arithmetic symmetric modulus S(X) = (|X|+|X*|)/2 and ordinary positive-semidefinite order, allowing two arbitrary complex unitaries depending on X,Y. Zhang's definition, Conjecture 1.6, and equation (1.4) agree with the manuscript. The quadratic symmetric modulus is a different object and its theorem does not resolve this target. [Zhang, arXiv v1, sections 1.1–1.2](https://arxiv.org/html/2603.01046v1#S1.SS2).

## Complete proof audit

1. For t>0 the displayed real X,Y are square 3-by-3 rank-one matrices, admissible within the unrestricted complex target. For nonzero u,v, the right and left Gram matrices of uv* give |uv*| = (||u||/||v||)vv* and |vu*| = (||v||/||u||)uu*. No singular inverse or zero-vector case is used.

2. Write s = sqrt(1+t²). For X, S(X) equals s/2 times the sum of projections onto e_1 and (e_1+t e_2)/s. The eigenvalues of the sum of these projections on their span are 1±1/s, so the full eigenvalue list is (s+1)/2, (s-1)/2, 0. The same calculation for Y uses e_3 in place of e_2; the minus sign of Y disappears in both moduli. This verifies both eigenvalue lists, their decreasing ordering, and their strict top eigenspaces for t>0.

3. The sum t(e_1e_2* - e_3e_1*) maps e_1 to -t e_3, e_2 to t e_1, and e_3 to zero. Thus its right modulus is t diag(1,1,0) and its left modulus is t diag(1,0,1). Their arithmetic mean is diag(t,t/2,t/2), giving the uniform lower bound tI/2 in every direction.

4. For every pair U,V of complex unitaries, two selected unit top eigenvectors span a subspace of dimension at most two. Its orthogonal complement in complex dimension three contains a unit vector w. On this complement each conjugated modulus has Rayleigh quotient at most b=(s-1)/2. Hence the sum has quotient at most s-1. The vector may depend on U,V; this is exactly what is required to defeat every proposed pair. No simultaneous diagonalization of the two moduli is assumed.

5. A domination with nonnegative C would imply t/2 ≤ C(s-1), and since s-1>0 this gives C ≥ (s+1)/(2t). That expression diverges as t decreases to zero. Thus for each finite C a positive t excludes all choices of U,V, even with the dimension fixed. This correctly reverses the existential-unitary quantifier in the target. C=0 is excluded by the positive left-hand side as well.

6. At t=3/4, s=5/4, a=9/8 and b=1/8. Direct substitution into the rank-one formula gives the two rational matrices printed in the manuscript. The two-orbit Rayleigh upper bound after multiplying by sqrt(2) is sqrt(2)/4, strictly less than 3/8 because 2sqrt(2)<3. Thus the fixed rational example already disproves the canonical sqrt(2) statement without an asymptotic argument.

## Scope and limitations

No material gap was found. The construction refutes ordinary matrix-order domination; it does not refute a separate unitarily invariant norm statement. No assertion about the optimal situation in dimension two is required. Algebraic computation and the complement-dimension argument provide the proof; diagnostics are unnecessary. This is independent agent review, not external human peer review, formal verification, or an exhaustive novelty/priority search. No canonical or original proof edits were made.
