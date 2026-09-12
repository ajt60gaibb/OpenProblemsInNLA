---
title: "SP-12: The chromatic nullity bound from Hall's theorem"
author: George Stepaniants
affiliation: Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA.
date: 11 September 2026
document-kind: APPLICATION NOTE
review-footer: "Hall's theorem; AI-assisted application note and independent automated-agent review."
---

\pagestyle{plain}

**Literature-dependent resolution.** The all-graph theorem used here is due to H. Tracy Hall. This application note was prepared with substantial ChatGPT/Codex assistance. A separate [independent Codex-agent review](../../references/stepaniants-sp11-sp12-2026-09-11/verification/SP-11-SP-12-independent-review.md) checked this deduction and the essential proof of Hall's theorem and returned **PASS**. This is automated-agent mathematical review, not external human peer review, formal verification, or a claim that the cited preprint has been refereed.

## Statement and external input

Let $G$ be a finite simple undirected graph on $n\ge1$ vertices. Let $\mathcal S(G)$ be the real symmetric $n\times n$ matrices with off-diagonal nonzero entries exactly at the edges of $G$ and unrestricted diagonal. A matrix $A\in\mathcal S(G)$ has the strong Arnold property (SAP) when the only real symmetric $X$ satisfying

$$
AX=0,\qquad A\circ X=0,\qquad I_n\circ X=0
$$

is $X=0$. Here $\circ$ is entrywise product. Define

$$
\nu(G)=\max\{\operatorname{nullity}A:
A\in\mathcal S(G),\ A\succeq0,\ A\text{ has SAP}\}.
$$

The target is $\nu(G)\ge\chi(G)-1$, where $\chi(G)$ is the chromatic number. The principal external input is Hall's **Corollary 3.22**, based on **Theorem 3.20**:

$$\nu(F)\ge\delta(F)\qquad\text{for every finite simple graph }F.\tag{H}$$

The source [H] is the preprint arXiv:2601.01211v1, submitted 3 January 2026. Its current record still listed only v1 when checked on 11 September 2026. This note supplies the remaining implication explicitly. The independent review checked the essential proof of (H); it also documents nonessential wording issues, including "positive definite" in the abstract where the definitions and construction use positive semidefinite matrices.

\Needspace{7\baselineskip}
## Lemma: induced-subgraph monotonicity

If $H$ is an induced subgraph of $G$, then $\nu(H)\le\nu(G)$.

### Proof for adding one vertex

It suffices to treat $G$ obtained by adding one vertex $v$ to $H$. Let $H$ have $h$ vertices. Choose a PSD matrix $A\in\mathcal S(H)$ with SAP and rank $r$. We construct a PSD SAP matrix in $\mathcal S(G)$ with rank $r+1$, preserving nullity.

Let $\mathcal M_r$ be the smooth manifold of $h\times h$ PSD symmetric matrices of rank $r$ near $A$. Let $P$ send a symmetric matrix to its entries at unordered nonedges of $H$. We first show that the differential of $P|_{\mathcal M_r}$ is surjective at $A$.

In an orthonormal basis adapted to the range and kernel of $A$, tangent matrices have the form

$$
\begin{pmatrix}S&T\\T^T&0\end{pmatrix},
$$

where $S$ is an arbitrary symmetric $r\times r$ matrix and $T$ is arbitrary. Its orthogonal complement in the space of symmetric matrices is exactly the symmetric matrices $X$ with $AX=0$. If the differential of $P$ were not onto, its adjoint would give a nonzero such normal matrix supported only on off-diagonal nonedges of $H$. This contradicts SAP. The differential is therefore surjective.

Write $z_i=1$ when vertex $i$ is adjacent to $v$ in $G$ and $z_i=0$ otherwise, and set $b=\epsilon z$. The submersion theorem gives matrices $D_\epsilon\in\mathcal M_r$, converging to $A$ as $\epsilon\to0$, with

$$
(D_\epsilon)_{ij}=-b_i b_j
$$

at each nonedge $\{i,j\}$ of $H$. Define

$$
B_\epsilon=\begin{pmatrix}1&b^T\\b&D_\epsilon+bb^T\end{pmatrix}.
$$

Its Schur complement is $D_\epsilon$, so $B_\epsilon$ is PSD of rank $r+1$. Old nonedges cancel exactly; old edges remain nonzero for sufficiently small $\epsilon$ because they converge to those of $A$. For nonzero $\epsilon$, new edges are exactly the nonzero coordinates of $b$. Thus $B_\epsilon\in\mathcal S(G)$.

To check SAP, let $Z_G$ be the fixed vector space of symmetric matrices with zero diagonal and zero entries on every edge of $G$. At

$$B_0=\operatorname{diag}(1,A),$$

the map $X\mapsto B_0X$ on $Z_G$ is injective. Its first row forces the first row of $X$ to vanish; symmetry then forces its first column to vanish. The remaining block $X_H$ satisfies $AX_H=0$ and is supported on off-diagonal nonedges of $H$, so SAP for $A$ forces $X_H=0$.

Injectivity of a linear map between finite-dimensional spaces is open in its matrix entries: a nonzero maximal-column-rank minor remains nonzero under sufficiently small perturbations. Hence $X\mapsto B_\epsilon X$ stays injective on $Z_G$ for small $\epsilon$. Since $B_\epsilon$ has exactly the pattern $G$, this is its SAP.

Nullity has been preserved:

$$
\operatorname{nullity}B_\epsilon=(h+1)-(r+1)=h-r.
$$

Choose $A$ with nullity $\nu(H)$ and add the omitted vertices one at a time. This proves the lemma. The rank-zero case is included: $\mathcal M_0=\{0\}$ is a zero-dimensional manifold, and surjectivity is forced by SAP as above. No connectedness assumption is used. $\square$

\Needspace{7\baselineskip}
## The chromatic bound: affirmative answer to SP-12

Set $k=\chi(G)$. Choose an induced subgraph $H$ minimal in vertex count subject to $\chi(H)=k$. For $k\ge2$, deleting any vertex of $H$ leaves a graph colorable with at most $k-1$ colors. If a vertex had degree at most $k-2$, such a coloring after its deletion would leave an unused color among its neighbors and would extend to $H$, a contradiction. Therefore $\delta(H)\ge k-1$.

Combine the lemma, Hall's theorem (H), and this degree inequality:

$$
\nu(G)\ge\nu(H)\ge\delta(H)\ge k-1=\chi(G)-1.
$$

For $k=1$, the target $\nu(G)\ge0$ is immediate. This proves the exact all-graph assertion without assuming Hadwiger's conjecture. $\square$

## Scope and attribution

Hall's all-graph theorem is the essential external input. George Stepaniants is the author of this explanatory application note, not the discoverer of Hall's theorem. No novelty is asserted for induced-subgraph monotonicity or the chromatic implication, which the original problem source already identifies as following from Strong Delta. The note does not provide a new independent proof of the central existence theorem.

The [submission record](../../references/stepaniants-sp11-sp12-2026-09-11/README.md) preserves the reconstructed source, independent review and dated public-network audit. Unsupported earlier claims about unavailable artifacts and graph-atlas computations remain withdrawn.

## References

[H] H. Tracy Hall, *The Delta Theorem: A dimension bound for faithful orthogonal graph representations*, arXiv:2601.01211v1, 3 January 2026, Theorem 3.20 and Corollary 3.22. [Versioned primary text](https://arxiv.org/html/2601.01211v1) · [Current arXiv record](https://arxiv.org/abs/2601.01211).

[R12] *Open Problems in Numerical Linear Algebra*, [SP-12: original canonical target and references](README.md).
