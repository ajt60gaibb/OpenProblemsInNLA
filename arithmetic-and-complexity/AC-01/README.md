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
reports $`\omega<2.371177`$. The October 2026 manuscript below reports a
stronger upper bound. An exponent-two claim is recorded separately with its
verification limits. **Admitted: no validated resolution located.**

## Status check — 2026-09-10

Rechecked [Dupont et al., August 2026](https://arxiv.org/abs/2608.16884), and searched for exponent-two proofs and newer matrix-multiplication bounds. Its reported bound is still strictly above two, at 2.371177. No proof of exponent two or a strict lower bound above two was located. Faster finite-size identities and improved numerical optimizations of existing bounds do not decide the asymptotic equality.

## Reviewed research submission — 14 September 2026

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation. [Verified affiliation and submission record](../../references/holden-ac-2026-09-14/README.md).

Sections 4–8 prove the auxiliary bound $`\widetilde R(\mathrm{cw}_2)<3.876919161`$, also relevant to [AC-04](../AC-04/README.md). The Section 10 scalar-tree obstruction is not a tensor-rank lower bound. Neither result proves $`\omega=2`$.

**Status: Open.** [Report](../../references/holden-ac-2026-09-14/AC-01-submission.pdf) · [Independent AI-agent audit and limitations](../../references/holden-ac-2026-09-14/verification/review-ac01-ac02.md). AI assistance disclosed; no external human review, formal verification or Lean checks. Original target and prior-source credit retained.

## Literature update — 2026-10-06

OpenAI, [*An Upper Bound of 9/4 for the Matrix Multiplication
Exponent*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Matrix-Multiplication-Nine-Fourths-October-2-2026/paper.pdf),
manuscript dated 2 October 2026, Theorem 1.1, reports that, for every
$`\varepsilon>0`$, complex $`n\times n`$ matrix multiplication uses
$`O_{\varepsilon}(n^{9/4+\varepsilon})`$ arithmetic operations, hence
$`\omega(\mathbb C)\le9/4=2.25`$. The
[theorem source](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Matrix-Multiplication-Nine-Fourths-October-2-2026/build/paper.tex)
and the release's [Lean scope note, “Scope”](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/107.md)
are pinned to revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The scope
note reports an unconditional formalization for finite division-free arithmetic
programs with arbitrary positive exponent slack, which fits the arithmetic
model in this entry. This update reviewed the statement and published scope;
it did not rerun Lean or independently audit the proof. The reported upper
bound improves the August bound cited above but leaves $`\omega=2`$ open.

### Unvalidated exponent-two claim — 18 September 2026

Zhi-Wei Sun, [*Tensor Degenerations for Matrix
Multiplication*](https://chinaxiv.org/abs/202609.00167), ChinaXiv:202609.00167.
The original [Math-ChinaXiv index](https://math.chinaxiv.org/server/mathindex.htm?locale=en)
lists this title with date 18 September 2026. A
[reproduced author abstract](https://chinarxiv.org/items/chinaxiv-202609.00167)
claims that, for every positive integer $`n`$ and every field $`\mathbb K`$,
the border rank of the $`2^n\times2^n`$ multiplication tensor is at most
$`2^{2n+1}`$, and claims the consequence $`\omega(\mathbb K)=2`$.
If established over $`\mathbb C`$, this would settle the displayed target.
During this check the original abstract and PDF endpoints returned HTTP 403;
the proof was inaccessible. The inspected evidence consists of the original
title/date listing and the reproduced abstract. No independent validation was
located, and this catalog has not checked the argument. This remains an
unvalidated full-resolution claim and does not change the **Open** status.
