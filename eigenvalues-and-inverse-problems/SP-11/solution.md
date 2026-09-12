---
title: "SP-11: The delta bound from Hall's theorem"
author: George Stepaniants
affiliation: Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA.
date: 11 September 2026
document-kind: APPLICATION NOTE
review-footer: "Hall's theorem; AI-assisted application note and independent automated-agent review."
---

\pagestyle{plain}

**Literature-dependent resolution.** The all-graph theorem used here is due to H. Tracy Hall. This application note was prepared with substantial ChatGPT/Codex assistance. A separate [independent Codex-agent review](../../references/stepaniants-sp11-sp12-2026-09-11/verification/SP-11-SP-12-independent-review.md) checked this deduction and the essential proof of Hall's theorem and returned **PASS**. This is automated-agent mathematical review, not external human peer review, formal verification, or a claim that the cited preprint has been refereed.

## Statement and notation

Let $G$ be a finite simple undirected graph on $n\ge1$ vertices, and let $\mathcal S(G)$ be the real symmetric $n\times n$ matrices whose off-diagonal nonzero entries occur exactly at the edges of $G$. Diagonal entries are unrestricted. Writing $\delta(G)$ for the minimum vertex degree, the target is

$$
\operatorname{mr}(G):=\min_{A\in\mathcal S(G)}\operatorname{rank}A
\le n-\delta(G).
$$

Define $\nu(G)$ as the maximum nullity among positive-semidefinite $A\in\mathcal S(G)$ satisfying the strong Arnold property (SAP): the only real symmetric $X$ with

$$
AX=0,\qquad A\circ X=0,\qquad I_n\circ X=0
$$

is $X=0$, where $\circ$ denotes entrywise product.

## External theorem

Hall's **Corollary 3.22**, based on **Theorem 3.20**, proves

$$\nu(G)\ge\delta(G)$$

for every finite simple graph [H]. The source is arXiv:2601.01211v1, submitted 3 January 2026; the current record still listed only v1 when checked on 11 September 2026. The theorem is used as an external input here. The independent review records its full essential proof audit and the nonessential wording issues in the source. In particular, the matrix in the definitions and Gram construction is positive **semidefinite**, despite the word "definite" in the abstract.

## Deduction: affirmative answer to SP-11

Choose a positive-semidefinite SAP matrix $A\in\mathcal S(G)$ with nullity at least $\delta(G)$, as provided by [H]. Forgetting the extra PSD and SAP conditions leaves an admissible matrix for SP-11. Rank-nullity gives

$$
\operatorname{mr}(G)\le\operatorname{rank}A
=n-\operatorname{nullity}A\le n-\delta(G).
$$

This is exactly the requested inequality. No connectedness assumption, prescribed edge weights, or diagonal restriction is introduced. When $\delta(G)=0$, the bound also holds trivially. $\square$

## Attribution and scope

The substantive all-graph existence theorem belongs to Hall. His **Corollary 3.24** explicitly states the ordinary Delta Conjecture as a consequence. George Stepaniants is the author of this explanatory application note, not the discoverer of that theorem. No novelty or priority claim is made.

The [submission record](../../references/stepaniants-sp11-sp12-2026-09-11/README.md) preserves the original reconstructed note, the independent review, and the dated public-network audit. Unsupported earlier claims about unavailable artifacts and graph-atlas computations remain withdrawn; they are not evidence for this resolution.

## References

[H] H. Tracy Hall, *The Delta Theorem: A dimension bound for faithful orthogonal graph representations*, arXiv:2601.01211v1, 3 January 2026, Theorem 3.20 and Corollaries 3.22-3.24. [Versioned primary text](https://arxiv.org/html/2601.01211v1) · [Current arXiv record](https://arxiv.org/abs/2601.01211).

[R11] *Open Problems in Numerical Linear Algebra*, [SP-11: original canonical target](README.md).
