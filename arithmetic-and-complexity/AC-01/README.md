# AC-01 — Is the matrix multiplication exponent two?

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Rating rationale:** Extreme because closing the exponent gap is a longstanding central barrier in algebraic algorithms; broad importance follows from matrix multiplication’s role throughout NLA and computational complexity.  
**Topic:** arithmetic complexity of dense matrix multiplication  
**Last checked:** 2026-10-06  
**Status:** Open  

## Problem statement

Over the field $`\mathbb C`$, let $`M(n)`$ be the minimum number of
scalar additions, subtractions, multiplications, and divisions in an arithmetic
straight-line program computing every entry of $`AB`$ for arbitrary
$`A,B\in\mathbb C^{n\times n}`$. Programs must be defined on their intended inputs.
Set $`\omega=\inf\{\tau:M(n)=O(n^\tau)\}`$. Is $`\omega=2`$? Equivalently, for every
$`\varepsilon>0`$, can these products be computed in $`O(n^{2+\varepsilon})`$
arithmetic operations? This asks about asymptotic arithmetic cost; it does not
assert an $`O(n^2)`$ algorithm or a floating-point stability guarantee.

## Why it matters

Matrix multiplication is a basic cost driver for dense NLA.

## References and status

M. Bläser, [*Fast Matrix Multiplication*](https://theoryofcomputing.org/articles/gs005/gs005.pdf),
Graduate Surveys 5 (2013), §§1, 5, provides the computational model. E. Dupont
et al., [*Improving the matrix multiplication exponent with modern optimization
and AlphaEvolve*](https://arxiv.org/abs/2608.16884) (2026), abstract and §1,
reported the earlier bound $`\omega<2.371177`$. OpenAI,
[*An Upper Bound of 9/4 for the Matrix Multiplication Exponent*](https://github.com/openai/math/blob/main/preprints/Matrix-Multiplication-Nine-Fourths-October-2-2026/paper.pdf)
(2 October 2026), reports $`\omega\leq 9/4=2.25`$ over $`\mathbb C`$.
The bound is strictly above two. **Admitted: no resolution located.**

## Status check — 2026-09-10

Rechecked [Dupont et al., August 2026](https://arxiv.org/abs/2608.16884), and searched for exponent-two proofs and newer matrix-multiplication bounds. Its reported bound is still strictly above two, at 2.371177. No proof of exponent two or a strict lower bound above two was located. Faster finite-size identities and improved numerical optimizations of existing bounds do not decide the asymptotic equality.

## Status check — 2026-10-06

[OpenAI's mathematics release](https://openai.com/index/sharing-ai-progress-in-mathematics/) points to its [manuscript catalogue](https://github.com/openai/math/blob/main/CONTENTS.md), which lists the 9/4 square-matrix bound over $`\mathbb C`$ and the [preprint](https://github.com/openai/math/blob/main/preprints/Matrix-Multiplication-Nine-Fourths-October-2-2026/paper.pdf). This is a reported $`O_\varepsilon(n^{9/4+\varepsilon})`$ arithmetic-operation upper bound, improving the previously cited 2.371177 bound. The new claim has not been independently reviewed for this entry. Since $`9/4>2`$, it does not answer whether $`\omega=2`$; **AC-01 remains open**.

## Reviewed research submission — 14 September 2026

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation. [Verified affiliation and submission record](../../references/holden-ac-2026-09-14/README.md).

Sections 4–8 prove the auxiliary bound $`\widetilde R(\mathrm{cw}_2)<3.876919161`$, also relevant to [AC-04](../AC-04/README.md). The Section 10 scalar-tree obstruction is not a tensor-rank lower bound. Neither result proves $`\omega=2`$.

**Status: Open.** [Report](../../references/holden-ac-2026-09-14/AC-01-submission.pdf) · [Independent AI-agent audit and limitations](../../references/holden-ac-2026-09-14/verification/review-ac01-ac02.md). AI assistance disclosed; no external human review, formal verification or Lean checks. Original target and prior-source credit retained.
