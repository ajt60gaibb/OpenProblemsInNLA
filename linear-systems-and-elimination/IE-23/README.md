# IE-23 — Uniqueness of the right inverse minimizing an induced p-to-2 norm

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** hard  
**Importance:** interesting to specialist  
**Status:** Open  
**Last checked:** 2026-09-10  

**Rating rationale:** Hard reflects a focused uniqueness question for a known norm minimizer; specialist impact is the characterization of generalized inverses under induced norms.

## Problem statement

Let $1\le m<n$, let $A\in\mathbb C^{m\times n}$ have rank $m$, and let $2<p<\infty$. For $X\in\mathbb C^{n\times m}$ define the induced norm

$$
\|X\|_{p\to2}=\sup_{y\in\mathbb C^m\setminus\{0\}}
\frac{\|Xy\|_2}{\bigl(\sum_{i=1}^m|y_i|^p\bigr)^{1/p}}.
$$

The Moore–Penrose inverse $A^\dagger=A^*(AA^*)^{-1}$ minimizes this norm among the right inverses $X$ satisfying $AX=I_m$. Is it always the unique minimizer? Equivalently, must

$$
AX=I_m,\quad X\ne A^\dagger
\quad\Longrightarrow\quad
\|X\|_{p\to2}>\|A^\dagger\|_{p\to2}
$$

hold for every such $A,p,X$?

This is the direct-inverse uniqueness question in Dokmanić–Gribonval's Remark 4.1. The endpoints and the separate objective $\|XA\|_{p\to2}$ are outside this statement.

## Connection to numerical linear algebra

The norm measures the worst Euclidean solution amplification for right-hand sides bounded in $\ell^p$. Uniqueness determines whether another linear solver can match the Moore–Penrose inverse's optimal amplification while changing its sparsity or structure.

## References

1. I. Dokmanić and R. Gribonval, *Beyond Moore–Penrose Part I: Generalized Inverses that Minimize Matrix Norms*, arXiv:1706.08349v2 (2017), §2.1 and §2.4 (right inverses and $A^\dagger$); §4.4, Corollary 4.2(3) and Remark 4.1, manuscript p. 18 (PDF page 18). [Preprint and version history](https://arxiv.org/abs/1706.08349). [PDF](https://arxiv.org/pdf/1706.08349).
2. I. Dokmanić and R. Gribonval, [*Part II: The Sparse Pseudoinverse*](https://arxiv.org/abs/1706.08701), 2017, §2. Its entrywise-norm objective is different.

## Earlier status check — 2026-09-08

Checked the complete v2 statement and version history on 2026-09-08; v2, dated 2017-07-13, remains the latest arXiv version of Part I. Searches combined the authors, the paper title, “induced norm”, “p to 2”, “unique”, “uniqueness”, “generalized inverse”, and 2025/2026. The companion paper's sparse-inverse uniqueness results concern entrywise norms and generic inputs, not this induced-norm claim for every full-row-rank matrix. No later proof or counterexample was located. This bounded search does not certify that no resolution exists elsewhere.

## Audit update — 2026-09-10

The [author copy of Part I](https://dokmanic.ece.illinois.edu/assets/pdf/DokmanicG17aa.pdf), Corollary 4.2(3) and Remark 4.1 on printed p. 18, explicitly separates minimality from the remaining uniqueness question for $2<p<\infty$. Searches for later induced-$p$-to-2 uniqueness results found no resolution; Part II's sparse-inverse objectives do not supply this missing assertion.
