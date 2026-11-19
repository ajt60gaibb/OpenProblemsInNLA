# MF-11 — Temporal regularity of marginal matrix-product growth

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Rating rationale:** Challenging because cancellations across coupled blocks resist general growth regularity; its immediate impact is on specialists in marginally stable matrix products. These ratings are historical assessments of the original target.

**Status:** Solution claimed

**Last checked:** 2026-11-19

## Negative resolution claimed - 19 November 2026

Pedro Martins, [*Marginal Growth Rates of Matrix Products Need Not Be Weakly
Increasing or Regularly Varying*](https://doi.org/10.5281/zenodo.24237543),
published as a preprint on **15 November 2026**, reports a negative answer to
both questions. **Theorem 1.3** (p. 2; construction and proof in Sections 2-5,
pp. 4-13) gives a pair of real $`20\times20`$ matrices
$`\mathcal M_{\theta_\star}=\{F_0(\theta_\star),F_1(\theta_\star)\}`$.
Writing $`g=g_{\mathcal M_{\theta_\star}}`$, the theorem asserts

```math
n\le g(n)\le6n^3\qquad(n\ge1),
```

which implies $`\widehat\rho(\mathcal M_{\theta_\star})=1`$. For
$`p_1=4`$, $`p_{j+1}=4^{p_j}`$,
$`\theta_\star=\sum_{j\ge1}p_j^{-1}`$ and $`N_j=16^{p_j}`$, it also asserts,
for every $`j\ge2`$ and every integer $`\ell\ge2`$,

```math
\frac{g(N_j/2)}{g(N_j)}\ge\frac{2^{p_j}}{4\cdot10^5p_j^4},
\qquad
\frac{g(\ell N_j)}{g(N_j)}\ge
\frac{(\ell-1)2^{p_j}}{4\cdot10^5p_j^4}.
```

The factors on the right tend to infinity. The first ratio contradicts a
fixed weak-increase constant by taking $`k=N_j/2`$ and the time increment
$`N_j/2`$ in the original statement. The second contradicts weak upper
regular variation already for the fixed multiplier $`\ell=2`$. A pair of
real matrices is compact and nonempty, and the theorem uses the same
Euclidean operator norm and maximum over all words as this entry. Thus the
reported result covers both complete universal targets, rather than only
growth along a selected switching word. The original definitions, questions
and earlier literature checks are retained below.

**Evidence and review scope.** The [retained submission](../../references/martins-mf11-2026-11-19/README.md)
contains the 35-page manuscript, the three supplied Python scripts, the Lean
attachment and their file identities. The [assessment and reproduction record](../../references/martins-mf11-2026-11-19/verification/README.md)
checks the target correspondence and main construction and records fresh
finite computations. These checks do not constitute an independent
full-result proof audit, external human peer review or formal verification;
the status is **Solution claimed**, as requested in
[issue #385](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/385).

The attached Lean source includes declarations named
`MF11.MF11_negative_answer_spectral` and `MF11.MF11_answer_is_no`, but the
attachment supplies no pinned toolchain/dependency project or reproducible
kernel-checking record. The catalog has not compiled or kernel-checked it.
No **Lean verified** status is asserted. The manuscript discloses Claude
assistance with drafting, editing and verification scripts, with the author
taking responsibility for the content.

## Context and notation

The joint spectral radius of a nonempty compact set $`\mathcal M\subset\mathbb C^{d\times d}`$ is

```math
\widehat\rho(\mathcal M)=\lim_{k\to\infty}
\max_{A_1,\ldots,A_k\in\mathcal M}\|A_k\cdots A_1\|_2^{1/k}.
```

This definition also applies to finite real matrix sets. The ordinary spectral
radius of one matrix is written $`\rho(A)`$.

For a compact nonempty $`\mathcal M\subset\mathbb R^{d\times d}`$ with
$`\widehat\rho(\mathcal M)=1`$, define its maximal product norm at length $`k`$ by

```math
g_{\mathcal M}(k)=\max_{A_1,\ldots,A_k\in\mathcal M}\|A_k\cdots A_1\|_2.
```

This problem concerns growth within one family over time. [MF-07](../MF-07/README.md) instead requests
a dimension-dependent bound uniform across families.

## Problem statement

Does every family in this notation satisfy both

```math
\exists c>0\ \forall k,\ell\ge1:\quad
g_{\mathcal M}(k+\ell)\ge c\,g_{\mathcal M}(k)
```

and

```math
\forall \ell\ge1\ \exists C_\ell>0\ \forall k\ge1:\quad
g_{\mathcal M}(\ell k)\le C_\ell\,g_{\mathcal M}(k)?
```

Constants may depend on $`\mathcal M`$.

## Reference and status evidence

Varney and Morris,
[On marginal growth rates of matrix products](https://arxiv.org/html/2209.00449),
Linear Algebra Appl. 709 (2025), 132–163,
[DOI](https://doi.org/10.1016/j.laa.2025.01.013), §4, Definition 4.1 and §7,
Question 1. The source names these properties weak increase and weak upper regular
variation. Searches for both property names, the authors, and subsequent
matrix-product growth papers located no resolution.

## Audit — 2026-09-10

Rechecked [Varney–Morris, §7, Question 1](https://arxiv.org/html/2209.00449). Both weak increase and weak upper regular variation remain posed; the source explains why cancellation defeats its current argument. Property-name and author follow-up searches found no resolution of the two-part target.
