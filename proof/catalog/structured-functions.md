# Structured matrix functions

> Legacy source map and screening notes. Admitted statements have moved to category/problem folders. Follow the links below or [browse the new index](../../CATALOG.md). Shared notation and uncounted material are retained here as the historical source record.

This chapter admits one problem. Two further source-backed research directions
are retained below as **uncounted candidates** because a fully justified,
nontrivial quantitative formulation still needs work. The literature check date
is 2026-09-08.

<a id="sf-01"></a>

## SF-01 — Preservation of real H-matrix structure by Newton square-root iterates

[Open the problem folder](../../matrix-functions-and-stability/SF-01/README.md) · [PDF](../../matrix-functions-and-stability/SF-01/problem.pdf) · [LaTeX](../../matrix-functions-and-stability/SF-01/problem.tex)


## Uncounted candidate SF-02 — Conditioning versus roundoff in repeated squaring

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** withheld; the precise quantitative assertion below is an editorial
candidate, not a conjecture explicitly stated in the sources.

Let $A\in\mathbb R^{n\times n}\setminus\{0\}$,
$s=\max\{0,\lceil\log_2\|A\|_2\rceil\}$, and
$B_j=\exp(2^{j-s}A)$ for $0\le j\le s$.
For arbitrary real matrices $E_0,\ldots,E_{s-1}$ satisfying the entrywise
bounds $|E_j|\le |B_j||B_j|$, define

$$
F_0=0,\qquad
F_{j+1}=B_jF_j+F_jB_j+E_j.
$$

Let $L_{\exp}(A,\cdot)$ be the Fréchet derivative of the exponential and set

$$
\kappa_{\exp}(A)=
\frac{\|A\|_2}{\|\exp(A)\|_2}
\left(\sup_{\|E\|_2=1}\|L_{\exp}(A,E)\|_2\right).
$$

A possible fully explicit question is whether absolute constants $C>0$ and
$q\ge0$ give

$$
\sup_{|E_j|\le |B_j||B_j|}
\frac{\|F_s\|_2}{\|\exp(A)\|_2}
\le Cn^q(s+1)\kappa_{\exp}(A)
$$

uniformly in $n,A$. This models the first-order amplification of local
matrix-multiplication errors when the initial exponential is exact.
It is narrower than an analysis of the complete scaling-and-squaring algorithm.

**Source and remaining admission issue.** Higham, *Functions of Matrices*,
Research Problem 10.16, p. 266, asks for a stability analysis of the squaring
stage in relation to exponential conditioning. S. Güttel and Y. Nakatsukasa,
[*Scaled and Squared Subdiagonal Padé Approximation for the Matrix Exponential*](https://eprints.maths.manchester.ac.uk/2322/1/paperworkingmerge.pdf),
*SIAM J. Matrix Anal. Appl.* 37 (2016), 145–170, §§4 and 4.3, still describe
the general nonnormal stability issue as unresolved. The particular polynomial
factor in $n$ and linear factor in $s$ above are not extracted from either
source. Searches through 2026-09-08 did not justify calling that exact
assertion an established open problem, so it is not counted.

## Uncounted candidate SF-03 — Rank defects of the Toeplitz matrices in Fréchet–Jordan theory

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** explicitly open in a 2026 paper; withheld pending a precise
nontrivial criterion for an acceptable classification.

Take positive integers $m\le n$, $d$, and $\ell$ with $\ell d<m+n-1$.
For $1\le j\le m+n-1$, put $u_j=\min\{j,m,n,m+n-j\}$.
Define integers $\gamma_a$ by
$(1+z+\cdots+z^d)^\ell=\sum_{a=0}^{\ell d}\gamma_a z^a$ and put
$\gamma_a=0$ outside that range. For
$\ell d+1\le k\le m+n-1$, set

$$
c_k=\min\{\ell d,\max\{0,k-n\}\},\qquad
R_k=(\gamma_{j-i+c_k})_{
  1\le i\le u_{k-\ell d},\;1\le j\le u_k}.
$$

The target is an exact classification, in terms of these integer parameters,
of the rank defects

$$
\Delta(k,m,n,d,\ell)
=\min\{u_k,u_{k-\ell d}\}-\operatorname{rank}_{\mathbb Q}R_k.
$$

**Source and remaining admission issue.** V. Noferini,
[*The Jordan canonical form of the Fréchet derivative of a matrix function and
the bivariate Jordan problem*](https://arxiv.org/html/2512.08399v5)
(18 June 2026 version), Definition 4.10 and Problem 4.19, asks for all
rank-deficient parameter choices and their exact defects. Proposition 4.16
is sufficient but not necessary, as Example 4.18 shows. Searches through
2026-09-08 found no full classification. Computing each displayed finite
matrix's rank is already possible by exact elimination; merely asking for an
algorithm, or permitting a restatement through minors, would be vacuous.
An acceptable closed-form output class has not yet been specified without
introducing an unsupported complexity restriction. This candidate is therefore
not counted.

## Resolved or inadequately specified historical directions — not counted

- Higham's Research Problem 3.11, on the Jordan form of the Fréchet derivative,
  is resolved in Noferini's [June 2026 paper](https://arxiv.org/html/2512.08399v5),
  §4. Problem 4.19 above is a remaining refinement, not the original unresolved
  problem.
- Higham's Problems 6.24 and 6.26 concern choosing among iterations and designing
  direct algorithms for Cholesky factors. Without a specified accuracy/cost
  target they are research directions, not yet precise catalog assertions.
