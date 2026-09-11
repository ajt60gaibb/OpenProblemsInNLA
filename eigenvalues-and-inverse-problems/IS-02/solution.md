---
title: "IS-02: A counterexample to the spectral-uniqueness locus condition"
date: "11 September 2026"
lang: "en-GB"
---

**Status of this manuscript:** Proposed resolution, not independently verified.  
**Outcome claimed:** Negative resolution claim.  
**Prepared:** 11 September 2026.  
**Target:** [Repository entry IS-02](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/b4123194697bdf6f8f82518c1dd7d6c40a30c2e0/eigenvalues-and-inverse-problems/IS-02/README.md), snapshot `b412319`.

This is a proposed argument generated in a ChatGPT conversation and prepared for mathematical review. No independent referee report or formal proof certificate accompanies it. Supporting algebraic and numerical diagnostics are not a substitute for proof review. No publication or priority claim is made.

## Theorem IS-02: proposed counterexample

For real symmetric entrywise nonnegative stochastic matrices, define spectral uniqueness to mean uniqueness up to simultaneous permutation of rows and columns among matrices with the same spectrum, including multiplicity. Put
$$
C_n=\frac{\mathbf 1\mathbf 1^T-I_n}{n-1}.
$$
The proposed necessary condition places every spectrally unique matrix with positive trace, for $n\ge4$, in the union of $[I_n,C_n]$ and the segments $[I_n,V]$ and $[C_n,V]$ over vertices $V$ of the symmetric stochastic polytope.

**Claim.** The matrix
$$
A=\begin{pmatrix}
0&1&0&0\\
1&0&0&0\\
0&0&1/2&1/2\\
0&0&1/2&1/2
\end{pmatrix}
$$
is a counterexample.

### 1. Spectral uniqueness

The matrix is symmetric, nonnegative and stochastic. Its spectrum is $\{1,1,0,-1\}$ and its trace is one. Let $B$ be another real symmetric nonnegative stochastic matrix with this spectrum. For every real $x$,
$$
x^T(I-B)x=\frac12\sum_{i,j}b_{ij}(x_i-x_j)^2.
$$
The kernel consists of vectors constant on each connected component of the graph with an edge $ij$ when $i\ne j$ and $b_{ij}>0$. Thus the multiplicity of the eigenvalue one is the number of components, and $B$ has exactly two components.

Any connected component carrying the eigenvalue $-1$ has even order. To see this, restrict a nonzero real eigenvector $z$ with eigenvalue $-1$ to such a component. Then
$$
0=z^T(I+B)z=\frac12\sum_{i,j}b_{ij}(z_i+z_j)^2.
$$
Along any edge, $z_i=-z_j$. Connectivity implies that all coordinates have the same nonzero magnitude. The component is therefore bipartite, has no positive diagonal entries, and has no edges within either sign class. The total weight crossing from a sign class to the other is its number of vertices, by stochasticity. Symmetry makes the two crossing totals equal, so the two classes have equal cardinality.

There are four vertices and two nonempty components. The component carrying $-1$ must consequently have order two, and the other component also has order two. Every symmetric stochastic matrix of order two is
$$
B(t)=\begin{pmatrix}t&1-t\\1-t&t\end{pmatrix},
\qquad \sigma(B(t))=\{1,2t-1\}.
$$
The two blocks of $B$ must be $B(0)$ and $B(1/2)$. Therefore $B$ is permutation-similar to $A$, proving spectral uniqueness.

### 2. Exclusion from the asserted locus

Let $S=\begin{pmatrix}0&1\\1&0\end{pmatrix}$. The identity
$$
A=\tfrac12\operatorname{diag}(S,I_2)
  +\tfrac12\operatorname{diag}(S,S)
$$
is a nontrivial convex combination of two distinct symmetric stochastic matrices. Hence $A$ is not a vertex.

If $A=(1-t)I_4+tV$ with $0\le t\le1$ and $V$ a vertex, the zero entry $A_{11}$ and nonnegativity force $t=1$. This would give $A=V$, which is impossible.

If $A=(1-t)C_4+tV$, the zero entry $A_{13}$, together with $(C_4)_{13}=1/3$ and $V_{13}\ge0$, again forces $t=1$ and the same contradiction.

Finally, writing $A=(1-t)I_4+tC_4$, its zero $(1,3)$ entry forces $t=0$, whereas $A\ne I_4$. This excludes the remaining segment and completes the proposed negative resolution. $\square$

## Scope and review notes

The counterexample has n = 4, which is an allowed dimension. It uses entrywise nonnegativity, symmetry, row sums one, positive trace, and spectral uniqueness with multiplicities, exactly as in the entry. A counterexample in one allowed dimension refutes the universal necessary condition; a classification in all dimensions is not claimed.

Review should check the component argument for spectral uniqueness and the distinction between vertices of the symmetric stochastic polytope and permutation matrices. The proof does not assume those two vertex notions coincide.

The packaging pass checked the repository statement and contribution rules on 11 September 2026. It did not conduct a new exhaustive literature search or establish novelty.

## Source references

Alex Townsend, *Open Problems in Numerical Linear Algebra* (2026), [entry IS-02](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/b4123194697bdf6f8f82518c1dd7d6c40a30c2e0/eigenvalues-and-inverse-problems/IS-02/README.md), repository snapshot `b412319`, accessed 11 September 2026.

Mourad and Abbas, Conjecture 5.1, p. 10 of the [2013 manuscript](https://arxiv.org/abs/1310.1273); [published article](https://doi.org/10.1080/03081087.2014.903590), *Linear and Multilinear Algebra* 63 (2015), 869–881. These are the original-source locators given by the catalog.
