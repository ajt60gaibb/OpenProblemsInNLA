# MI-07 — The triangle conjecture for the maximal symmetric modulus

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Solved  
**Last checked:** 2026-09-11

**Rating rationale:** Combining spectral-order suprema with ordinary matrix-order domination requires new analysis; the immediate audience is operator-inequality specialists.

## Resolution — 2026-09-11

**Negative result by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent proof review: PASS.**

No finite two-unitary domination constant exists for the maximal symmetric modulus, already in dimension two. The rank-one family gives the necessary bound $C\ge\sqrt{1+t^2}/t$ for every $t>0$.

The exact target is resolved. The original statement and source evidence are retained below; its former difficulty rating is historical.

**Primary manuscript:** [complete proof PDF](solution.pdf), [standalone TeX](solution.tex), Theorem 1.1 and its proof; [authorship and scope](solution.md). The [independent review](../../references/colbrook-matrix-2026-09-11/verification/reviews/MI-07-review.md) checks the full original argument and records its hash. The draft was AI-assisted; this is independent agent verification, not external human peer review or formal certification. [Submission record](../../references/colbrook-matrix-2026-09-11/README.md).

## Problem statement

For a complex square matrix $X$, let $|X|=(X^*X)^{1/2}$ and define its maximal symmetric modulus by the finite-dimensional limit

$$M(X)=\lim_{r\to\infty}\bigl(|X|^r+|X^*|^r\bigr)^{1/r},\qquad r\in\mathbb N.$$

This is the supremum of $|X|$ and $|X^*|$ in Olson's spectral order. For every $n\ge1$ and every $A,B\in\mathbb C^{n\times n}$, must there exist unitary $U,V$ of order $n$ satisfying

$$M(A+B)\preceq U M(A)U^*+V M(B)V^*?$$

The order in this displayed inequality is ordinary positive-semidefinite order.

## Why it matters

The modulus combines both positive polar factors through spectral order. A sharp triangle inequality would give a new way to control positive representatives of nonnormal matrix sums.

## References

1. J.-C. Bourin and E.-Y. Lee, *Averages over matrix unitary orbits and spectral order*, arXiv:2606.15624v2 (18 June 2026), §§3.1–3.3, Question 3.11 and Conjecture 3.12. [Primary text](https://arxiv.org/html/2606.15624).
2. J.-C. Bourin and E.-Y. Lee, *Some hybrid matrix triangle inequalities*, arXiv:2606.29188v1 (28 June 2026), §3, Lemma 3.3 and Theorem 3.4. [Primary text](https://arxiv.org/html/2606.29188).

## Status check — 2026-09-10

Latest versions v2 and v1 were checked. The follow-up proves inequalities with the ordinary modulus of the total sum on the left, while the present conjecture has its maximal symmetric modulus there. Its conclusion therefore does not establish the displayed assertion. Searches included `maximal symmetric modulus conjecture`, `Bourin Lee 2606.15624 conjecture`, and `Some hybrid matrix triangle inequalities`. No later resolution was located.

**Audit update (2026-09-10):** Rechecked Bourin–Lee Conjecture 3.12 and their hybrid follow-up, then searched for maximal-modulus triangle results. The follow-up does not replace its left-hand ordinary modulus by the maximal modulus required here. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
