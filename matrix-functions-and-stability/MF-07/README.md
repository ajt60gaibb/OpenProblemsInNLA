# MF-07 — Uniform polynomial bounds for products at joint spectral radius one

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because the constant must be uniform over all families of a given dimension; community impact spans transient growth and stability analysis.  
**Status:** Solved  
**Last checked:** 2026-09-11  

<!-- colbrook-jsr-growth -->
## Resolution — 2026-09-11

**Affirmative resolution.** Matthew J. Colbrook's [complete manuscript, Theorem 1 and Proposition 5](../../references/colbrook-jsr-growth-2026-09-11/manuscripts/uniform_growth_and_holder.pdf) proves the displayed bound for every dimension and every nonempty compact complex matrix family of joint spectral radius one, with

$$
\Theta_1=1,\qquad
\Theta_d=d\left(\frac{2ed^2}{d-1}\right)^{d-1}\quad(d\ge2).
$$

This constant is independent of the family and its cardinality. The proof covers every switching word and every positive length, without irreducibility or an exact extremal norm. The growth exponent $d-1$ is sharp in general; the displayed constant is not asserted optimal. The result also holds for nonempty bounded real or complex families.

The complete original proof passed [independent Codex-agent review](../../references/colbrook-jsr-growth-2026-09-11/verification/reviews/MF-05-MF-07-review.md). [Authored TeX](../../references/colbrook-jsr-growth-2026-09-11/manuscripts/uniform_growth_and_holder.tex) · [Submission, authorship and verification record](../../references/colbrook-jsr-growth-2026-09-11/README.md). The proof was developed with AI assistance; no external human peer review or formal verification is claimed. The original statement and prior evidence below are retained, and the ratings above are historical. This entry no longer contributes to the open count.

<!-- /colbrook-jsr-growth -->

## Context and notation

Let $\mathcal H_d$ denote the nonempty compact subsets of
$\mathbb C^{d\times d}$.

The joint spectral radius of a nonempty compact set $\mathcal M\subset\mathbb C^{d\times d}$ is

$$
\widehat\rho(\mathcal M)=\lim_{k\to\infty}
\max_{A_1,\ldots,A_k\in\mathcal M}\|A_k\cdots A_1\|_2^{1/k}.
$$

This definition also applies to finite real matrix sets. The ordinary spectral
radius of one matrix is written $\rho(A)$.

## Problem statement

Does each $d\ge1$ admit $\Theta_d>0$ such that every
$\mathcal M\in\mathcal H_d$ with $\widehat\rho(\mathcal M)=1$ satisfies

$$
\|A_k\cdots A_1\|_2\le\Theta_d(Lk)^{d-1},\qquad
L=\max_{A\in\mathcal M}\|A\|_2,
$$

for all $k\ge1$ and all $A_1,\ldots,A_k\in\mathcal M$?

## Reference and status evidence

Epperlein and Wirth,
[The joint spectral radius is pointwise Hölder continuous](https://arxiv.org/html/2311.18633v2),
§2, Conjecture 3 (L3). Lemma 27 proves dimension two. The constant above must
be independent of the family.

## Common follow-up screen for [MF-05](../MF-05/README.md)–MF-07

Searches combining “joint spectral
radius” with “local Hölder”, “Lipschitz lower”, “trajectory bounds”, the authors'
names, and 2025/2026 found no later resolution. These searches supplement the
explicit 2025 conjectures; they do not establish exhaustiveness. The three entries
are separately named assertions in the source, not a count of dimensional cases.

## Audit — 2026-09-10

Rechecked [Conjecture 3 (L3) and Lemma 27](https://arxiv.org/html/2311.18633v2): dimension two is proved, but higher-dimensional uniform constants remain conjectural. Searches for trajectory bounds and subsequent Epperlein–Wirth work found no resolution. Family-dependent polynomial estimates do not establish the displayed uniform statement.
