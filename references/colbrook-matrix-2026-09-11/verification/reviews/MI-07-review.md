# MI-07 independent proof review

**Verdict: PASS — complete negative resolution of the exact canonical target; every finite two-unitary constant already fails in dimension two.**

Review date: 2026-09-11. Reviewer: independent agent `/root/review_matrix_orbits`. Canonical target: `matrix-inequalities-and-norms/MI-07/README.md`. Original read in full: `.cache/colbrook-matrix-submission/nla_submission/proofs/MI-07.tex`; the bundle preamble and bibliography were also read.

## Full original identity

SHA-256: `0a5351a8ee77d87faa491093ca801c0797227b7e70c3945d7368e16d9d733d2e`.

Hash procedure: decode the entire original file as strict UTF-8, replace CRLF by LF, re-encode as UTF-8, and hash, with no extraction, trimming, or other whitespace changes. Original and normalized lengths are both 2,285 bytes; no bare CR occurs. This review attaches to that full TeX identity, not to an extracted proof or independently rendered PDF.

## Target and source alignment

The canonical M is the limit of (|Z|^r+|Z*|^r)^(1/r) over positive integers; domination uses ordinary positive-semidefinite order. The pinned source identifies that limit with the spectral-order supremum in Proposition 3.6, defines the maximal symmetric modulus in section 3.3, and poses precisely the dimension-dependent constant and constant-one questions used here. [Bourin–Lee, arXiv v2, Proposition 3.6, Question 3.11 and Conjecture 3.12](https://arxiv.org/html/2606.15624v2#S3).

## Complete proof audit

1. The example A = e_1e_1* and B = t e_1e_2*, t>0, lies in the admissible real subset of complex 2-by-2 matrices. A is a projection, so its power expression is 2^(1/r)A and its limiting modulus is A. B has right modulus t e_2e_2* and left modulus t e_1e_1*; the sum of their r-th powers is t^r I. Its maximal symmetric modulus is therefore tI exactly, before any limiting subtlety.

2. For A+B = e_1(e_1+t e_2)*, let s=sqrt(1+t²) and v=(e_1+t e_2)/s. Its right and left moduli are s vv* and s e_1e_1*, respectively. Because these are scaled projections, raising to the r-th power gives s^r times each projection. Their combined power expression is therefore s(vv*+e_1e_1*)^(1/r), exactly as claimed.

3. For every fixed positive t, the two vectors v and e_1 are independent and span the whole space. The positive matrix R=vv*+e_1e_1* consequently has two positive eigenvalues, namely 1±1/s. By scalar functional calculus, each eigenvalue to the power 1/r tends to one. Hence R^(1/r) tends to I in finite-dimensional norm and M(A+B)=sI. The proof takes r to infinity at each fixed t, then considers t tending to zero; it does not interchange the limits or assume continuity of M at t=0. Such continuity would in fact be false for this example.

4. For arbitrary complex unitaries U,V, the right-hand orbit sum is (Ue_1)(Ue_1)* + tI. The second unitary has no effect. The eigenvalues are 1+t and t; testing a unit vector perpendicular to Ue_1 gives the necessary condition s ≤ Ct. This test works for every U,V. For C=1 it is impossible at every t>0 because s>t. For any fixed finite nonnegative C the ratio s/t diverges as t decreases to zero, giving a counterexample in the same dimension.

5. The fixed t=1/2 example has s=sqrt(5)/2 and the right-hand orbit-sum eigenvalues 3/2 and 1/2. It is an exact counterexample to the canonical constant-one assertion. The family, rather than that one example alone, proves that no finite constant works.

## Scope and limitations

No material gap was found. The theorem refutes the universal all-dimension conjecture and the existence of a finite constant at dimension two; the proof does not need to make a separate assertion about every larger fixed dimension. The left side is the maximal modulus, not the ordinary modulus, and the right-side comparison is not a spectral-order comparison. All calculations are exact and do not rely on numerical root approximations or diagnostics. This is independent agent review, not external human peer review, formal verification, or an exhaustive novelty/priority search. No canonical or original proof edits were made.
