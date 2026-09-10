# IV-06 — Number of components of a real interval eigenvalue set

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Open  
**Last checked:** 2026-09-10

**Rating rationale:** Controlling the topology of the real spectrum for nonsymmetric uncertain matrices appears to require new analysis, warranting challenging. The component-count bound primarily advances specialist interval spectral enclosure theory.

**Area:** interval linear algebra; eigenvalue computation  

## Problem statement

For every integer $n\ge1$ and real matrices $L,U\in\mathbb R^{n\times n}$ with $L\le U$ entrywise, form the interval matrix family

$$
\mathcal A=\{A\in\mathbb R^{n\times n}:L\le A\le U\}.
$$

Each entry varies independently in its prescribed closed interval; singleton intervals are allowed. Define the set of all real eigenvalues attained by the family by

$$
\Lambda_{\mathbb R}(\mathcal A)
=\{\lambda\in\mathbb R:\exists A\in\mathcal A,\ \exists x\in\mathbb R^n\setminus\{0\},\ Ax=\lambda x\}.
$$

Must $\Lambda_{\mathbb R}(\mathcal A)$ have at most $n$ connected components? Equivalently, must there exist $0\le m\le n$ and real numbers $a_r\le b_r$, $1\le r\le m$, such that

$$
\Lambda_{\mathbb R}(\mathcal A)=\bigcup_{r=1}^{m}[a_r,b_r]?
$$

The empty set corresponds to $m=0$, and a singleton eigenvalue component counts as one interval. No symmetry, diagonalizability, or reality of the entire spectrum is assumed. Only real eigenvalues contribute to the set.

Interval eigensolvers enclose all eigenvalues allowed by uncertain matrix entries. The conjecture bounds the number of separated real spectral regions they must represent, without claiming that their endpoints can be found efficiently. Finiteness and compactness of the union are known; the proposed linear bound is the unresolved claim. For families restricted to symmetric matrices, the ordered eigenvalue functions already give $n$ compact intervals, as explained in the second reference; that does not address the family above.

## References

Milan Hladík, David Daney, and Elias P. Tsigaridas, [*An algorithm for addressing the real interval eigenvalue problem*](https://doi.org/10.1016/j.cam.2010.11.022), Journal of Computational and Applied Mathematics **235** (2011), 2715–2730, §1, p. 2716, paragraph immediately after the definition of $\Lambda$.

The same authors, [*Characterizing and approximating eigenvalue sets of symmetric interval matrices*](https://www-sop.inria.fr/coprin/PDF/CAMWA6430.pdf), Computers & Mathematics with Applications **62** (2011), 3152–3163, §2, p. 3153; [DOI](https://doi.org/10.1016/j.camwa.2011.08.028).

## Status check

On 2026-09-10, checked the published formulation, the authors' follow-up on symmetric interval matrices, Hladík's current publication record, and searches for the original title, interval eigenvalue components, the at-most-$n$ claim, and 2025/2026 developments. No primary source proving or refuting the general conjecture was located. This is a bounded literature check; papers addressing only symmetric interval families do not settle the stated question.

## Independent audit — 2026-09-10

The primary 2011 JCAM text explicitly poses the at-most-$n$ conjecture for independent entries. The full symmetric follow-up instead studies the coupled family $\mathcal A^S=\{A\in\mathcal A:A=A^T\}$, generally a proper subset, as its §2 explains. Its result alone does not justify the previous partial-resolution label for the displayed independent-entry target. Targeted later component-count and exact-conjecture searches found no proof or counterexample; the explicit openness statement is historical.
