# MF-06 — A pointwise Lipschitz lower bound for the joint spectral radius

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because the sharp one-sided perturbation rate must survive reducibility; community impact is reliable lower stability estimates under data perturbation.  
**Status:** Solved  
**Last checked:** 2026-09-12  

## Affirmative resolution - 2026-09-12

**Author:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA.

**The full pointwise lower-Lipschitz assertion holds.** The [complete proof](solution.md), Theorem (1) and Sections 3-6, covers every fixed nonempty compact complex matrix family in every finite dimension, including reducible families with unbounded normalized products. For that fixed reference there are constants $C,r>0$ such that every nonempty compact family within Hausdorff distance $r$ satisfies the original lower bound below.

The proof establishes a product-bounded exterior-power family at a maximal critical degree and transfers a robust one-sided estimate back to the original family. The nearby family may be arbitrary; it need not preserve the reference's invariant subspaces. [Proof PDF](solution.pdf) · [Standalone proof TeX](solution.tex).

The complete clarified proof passed a separate [independent Codex-agent mathematical audit](../../references/stepaniants-mf06-2026-09-12/REVIEW.md). The [submission record](../../references/stepaniants-mf06-2026-09-12/README.md) contains the exact sources, source clarification, supplementary checks, document inspection and bounded public-network/source audit. Substantial AI assistance is disclosed; this is informal agent review, not external human peer review or formal verification.

Epperlein and Wirth retain attribution for the target. The Barabanov/Wirth extremal-norm theorem and Chitour-Mason-Sigalotti nonresonance theory retain credit; the proof supplies its needed paired-tensor arguments in full. The result is pointwise at a fixed family and does not claim a two-sided Lipschitz estimate uniform over two varying families. The original definitions, statement, historical partial status evidence and ratings below are retained.

## Context and notation

Let $\mathcal H_d$ denote the nonempty compact subsets of
$\mathbb C^{d\times d}$. Use the spectral norm and its Hausdorff distance

$$
d_H(\mathcal M,\mathcal N)=\max\left\{
\sup_{A\in\mathcal M}\inf_{B\in\mathcal N}\|A-B\|_2,
\sup_{B\in\mathcal N}\inf_{A\in\mathcal M}\|A-B\|_2\right\}.
$$

The joint spectral radius is

$$
\widehat\rho(\mathcal M)=\lim_{k\to\infty}
\max_{A_1,\ldots,A_k\in\mathcal M}\|A_k\cdots A_1\|_2^{1/k}.
$$

These definitions also apply to finite real matrix sets. The ordinary spectral
radius of one matrix is written $\rho(A)$.

## Problem statement

For every $d\ge1$ and $\mathcal M\in\mathcal H_d$, do
there exist $r,C>0$ such that

$$
\widehat\rho(\mathcal N)\ge\widehat\rho(\mathcal M)-C d_H(\mathcal M,\mathcal N)
\quad\text{if }d_H(\mathcal M,\mathcal N)<r?
$$

## Reference and status evidence

Epperlein and Wirth,
[The joint spectral radius is pointwise Hölder continuous](https://arxiv.org/html/2311.18633v2),
§2, Conjecture 3 (P2). The conjectured exponent is one.

## Scope

The reference family is fixed while the perturbed family varies. An
answer controls how rapidly a stability diagnostic can decrease under data error;
[MF-05](../MF-05/README.md) instead requires a two-sided estimate uniform over two varying families.

## Additional status evidence

Searches combining “joint spectral
radius” with “local Hölder”, “Lipschitz lower”, “trajectory bounds”, the authors'
names, and 2025/2026 found no later resolution. These searches supplement the
explicit 2025 conjectures; they do not establish exhaustiveness. The three entries
are separately named assertions in the source, not a count of dimensional cases.

## Audit — 2026-09-10

Rechecked [Epperlein–Wirth, §1 and Conjecture 3 (P2)](https://arxiv.org/html/2311.18633v2). Local Lipschitz continuity gives the asserted lower bound at irreducible families. The general reducible case remains posed, and searches for Lipschitz lower bounds and later author work found no resolution.
