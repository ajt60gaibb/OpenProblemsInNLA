# RE-06 — Nonadaptive queries for finite-family matrix approximation

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** open; checked 2026-09-08  
**Area:** nonadaptive matrix sketching  
**Last checked:** 2026-09-08  

## Context and notation

Use exact real arithmetic, with comparisons, standard Gaussian sampling, and exact SVDs available as primitives; charge an SVD of an $a\times b$ matrix $O(ab\min(a,b))$ operations. This states the idealized arithmetic model used here, rather than a finite precision or bit complexity claim. A matrix–vector query returns either $Av$ or $A^\mathsf Tv$ for one chosen real vector $v$; both types count toward the total. Randomized guarantees are for every fixed input, with probability or expectation over the algorithm's randomness.

## Problem statement

Let $n\ge1$, let $\mathcal F\subset\mathbb R^{n\times n}$ be explicitly given with $M=|\mathcal F|\ge2$, and let $A\in\mathbb R^{n\times n}$ be accessible only through matrix–vector queries. Set $t=\log(2M)$.

### Question

Do absolute constants $C>0$, integer $b\ge0$, and a uniform randomized algorithm exist that, for every $0<\varepsilon<1/2$, choose all query vectors and all choices between $A$ and $A^\mathsf T$ before receiving any oracle answers, make at most

$$
C\sqrt t\,\varepsilon^{-2}
\bigl[1+\log(2+t)+\log(1/\varepsilon)\bigr]^b
$$

queries, and return $B\in\mathcal F$ such that

$$
\Pr\!\left[\|A-B\|_F\le(3+\varepsilon)
\min_{D\in\mathcal F}\|A-D\|_F\right]\ge0.99?
$$

Query choices may depend on $\mathcal F,\varepsilon$ and randomness. Only oracle calls are charged; candidate processing and processing of the answers are unrestricted.

## References

Amsel et al., [*Query Efficient Structured Matrix Learning*](https://arxiv.org/html/2507.19290v2), §5, adaptivity question. Christopher Musco, [*Structured Matrix Learning from Matrix-Vector Products*](https://app.icerm.brown.edu/assets/568/10574/10574_5858_Musco_020420261630_Slides.pdf), ICERM, February 4, 2026, numbered slide 23.

## Status evidence

Both sources explicitly ask whether adaptivity is necessary; the paper's August 21, 2026 revision retains the question. Searches for “finite matrix approximation adaptivity 2026” and the paper identifier with “non-adaptive” found no resolution. The abstract's linked finite-family improvement, Theorem 1.2, uses two rounds after receiving a constant-factor warm start: its left query vectors depend on the first round's answers. It does not supply the required nonadaptive algorithm.
