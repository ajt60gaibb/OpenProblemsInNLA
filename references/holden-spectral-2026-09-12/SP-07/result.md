# SP-07 — a subclass matching lemma, not a sharp-constant determination

**Author:** Sidney Holden  
**Affiliation:** Center for Computational Biology, Flatiron Institute, Simons Foundation.  
**Submission date:** 12 September 2026.  
**Editorial record:** [Attribution, independent review and scope](../README.md).

The review statements below describe the supplied draft; the linked submission record records subsequent independent review.

**USEFUL REDUCTION / LEMMA.** Retain OPEN.

For normal A,B in C^{n x n} with spectra alpha_j,beta_j counted with algebraic
multiplicity, put d_infinity(A,B)=min_{pi in S_n} max_j |alpha_j-beta_{pi(j)}|.
The original target is the exact value of


```math
C_{\rm normal}=\sup_{n\ge2}\sup_{A\ne B\text{ normal}}
\frac{d_\infty(A,B)}{\|A-B\|_2}.
```


It is **not** a request to prove the already-refuted universal constant one.

Theorem 1 of `../SP-09/proof.md` proves, when at least one matrix has at most
two distinct eigenvalues, that d_infinity equals the minimum orbit distance.
Taking the identity unitary gives d_infinity(A,B)<=||A-B||_2 on that subclass.
The constant one is sharp there: A=diag(0,1), B=A+epsilon I, 0<epsilon<1/2.
Both the norm difference and bottleneck distance are epsilon.

The full proof of the supporting theorem is an explicit dependency in the pack,
not an external conjecture. Its scope and tests are in SP-09. It does not bound
the supremum over the remaining normal pairs, so it supplies no new global
upper or lower bound for C_normal and does not determine that scalar target.
A theorem for one restricted class is not a partial determination of a universal
sharp constant merely because it is a valid inequality.
