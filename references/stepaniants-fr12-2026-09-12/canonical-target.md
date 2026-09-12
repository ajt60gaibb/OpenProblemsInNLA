# FR-12 — Counting real Hadamard matrices

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Topic:** Enumeration of orthogonal sign matrices  
**Difficulty:** extreme  
**Importance:** interesting to the community  
**Status:** Open  
**Last checked:** 2026-09-11

**Rating rationale:** Known general upper bounds still have a quadratic exponent, while the conjecture asks for an exponent of order $n\log n$. The question concerns the abundance of exact flat orthogonal transforms, with connections to structured matrix constructions and elimination.

## Statement

For each positive integer $n$, let

$$
H(n)=\#\{A\in\{-1,1\}^{n\times n}:AA^{\mathsf T}=nI_n\}.
$$

**Conjecture.** There is an absolute constant $C>0$ such that

$$H(n)\le 2^{C n\log_2 n}$$

for every positive integer $n$ divisible by four.

The count is of individual matrices with their row and column labels. Matrices related by signed permutations are not identified. The statement does not require that a Hadamard matrix exist at every such order.

## Known bounds and numerical significance

Ferber, Jain and Zhao prove that some absolute $c_H>0$ gives
$H(n)\le 2^{(1-c_H)n^2/2}$ for every sufficiently large multiple of four.
Whenever $H(n)>0$, distinct row permutations of one Hadamard matrix give
$H(n)\ge n!$. Thus the conjectured exponent has the smallest possible order
along orders admitting such matrices.

Dividing a Hadamard matrix by $\sqrt n$ produces an orthogonal transformation
whose entries all have the same magnitude. The enumeration asks how many
exact sign designs can underlie these transforms. Peca-Medlin's work connects
Hadamard enumeration for butterfly constructions to structured orthogonal
matrices and Gaussian elimination. This is distinct from the Hadamard
existence conjecture and from bounds on elimination growth for a given matrix.

## References and status check

- A. Ferber, V. Jain and Y. Zhao, *On the number of Hadamard matrices via anti-concentration*, Combinatorics, Probability and Computing 31 (2022), 455–477. [DOI](https://doi.org/10.1017/S0963548321000377); [published PDF](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/887EFBBF79B804BCDD942029283D4CD7/S0963548321000377a.pdf/on_the_number_of_hadamard_matrices_via_anticoncentration.pdf). Conjecture 1.3 on p.456 is the displayed target; Theorem 1.2 gives the upper bound. The [arXiv record](https://arxiv.org/abs/1808.07222) also supplies the earlier manuscript, where the conjecture has different numbering.
- [BIRS workshop 24w5204 report (2024)](https://www.birs.ca/workshops/2024/24w5204/report24w5204.pdf), Conjecture 28, restates the enumeration target.
- J. Peca-Medlin, *Complete pivoting growth of butterfly matrices and butterfly Hadamard matrices* (2026). [DOI](https://doi.org/10.1080/03081087.2026.2660796), §3 before Proposition 3.1, discusses the general count as conjectural and enumerates specific butterfly constructions.

On 2026-09-11, checked the published statement and later restatements, and
searched the exact title, the authors' names, Hadamard enumeration, upper
bounds, and 2025–2026 proof/counterexample combinations. No full resolution
was located. The butterfly counts apply to restricted families and do not
settle this all-matrix upper bound. This is a bounded literature check.
