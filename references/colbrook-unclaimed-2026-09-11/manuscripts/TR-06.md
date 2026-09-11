---
title: "Finite mean angular conditioning from a bounded semialgebraic graph"
author: "Matthew J. Colbrook"
date: "11 September 2026"
---

Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom. Email: m.colbrook@damtp.cam.ac.uk.

This argument was developed with AI assistance at the author's request. Independent review is recorded separately; no priority claim or external human peer-review claim is made.

## 1. Statement and model

Fix a real tensor format with order $d\ge3$, mode sizes $n_j\ge2$, and rank $r\ge3$, subject to generic complex identifiability. Write $E$ for the ambient Euclidean tensor space with Frobenius norm. Let $M$ be the smooth identifiable real rank-$r$ locus equipped with its induced volume. As in the canonical TR-06 statement, the input density is
\[
d\mu(A)=Z^{-1}e^{-\|A\|^2/2}\,dV_M(A).
\]
For any local ordering of the unique rank-one summands, let $\Psi(A)=(a_1,\ldots,a_r)$ and
\[
f(A)=\left(\frac{a_1}{\|a_1\|},\ldots,\frac{a_r}{\|a_r\|}\right),
\qquad \kappa_{\rm ang}(A)=\|Df(A)\|_2.
\]
The derivative uses the induced tangent norm on $M$ and the product Frobenius norm on $E^r$. Changing the ordering is an isometry and does not change this norm.

**Theorem.** For every format and rank under these hypotheses, $\mathbb E_\mu\kappa_{\rm ang}<\infty$.

This is the volume-Gaussian input model of Beltran, Breiding and Vannieuwenhoven, Definition 1.3 in their preprint; their Conjecture 1.10 asks for this conclusion. It is not the distribution obtained by drawing summands independently. We prove integrability, not a format-uniform numerical upper bound or an efficient decomposition algorithm.

## 2. Bounded graphs control a first derivative

We use the standard finite-volume property of semialgebraic sets: a bounded semialgebraic set of dimension at most $s$ has finite $s$-dimensional Hausdorff measure. A precise reference is Hardt, Lambrechts, Turchin and Volic, Theorem 2.4. Closedness is not required.

Here is its application to a finite collection of local branches. Let $L\subset\mathbb R^a$ be a bounded smooth semialgebraic manifold of dimension $s\ge1$. Suppose $G\subset L\times\mathbb R^b$ is bounded and semialgebraic, its projection to $L$ has finite nonempty fibers, and locally it consists of smooth graphs of maps $g$. Assume every branch has the same derivative norm $K(x)$, as happens when branches differ by fixed coordinate permutations. Finite fibers imply $\dim G=s$. Thus $\mathcal H^s(G)<\infty$.

For a branch the graph embedding $x\mapsto(x,g(x))$ has volume Jacobian
\[
J_g(x)=\sqrt{\det(I+(Dg(x))^*Dg(x))}.
\]
If $\sigma_1,\ldots,\sigma_s$ are the singular values, including zeros, then
\[
J_g=\prod_{j=1}^s\sqrt{1+\sigma_j^2}\ge\max_j\sigma_j=K(x).
\]
The ordinary area formula on each smooth graph therefore gives
\[
\int_L K(x)\,dV_L(x)\le \mathcal H^s(G)<\infty. \tag{1}
\]
For precision, take a countable local graph cover and a disjoint measurable partition subordinate to its projection. On each piece count every distinct branch once. The area formula sums the Jacobians of those branches, and the sum is at least $K$. The corresponding graph pieces are disjoint. Monotone convergence proves (1), without assuming integrability or a global ordering in advance. Lower-dimensional semialgebraic pieces may be removed without affecting either integral. Equivalently one may first use a finite smooth semialgebraic stratification. Only local graph calculus and the cited bounded-volume theorem are used here.

## 3. The normalized decomposition graph

The cone of nonzero rank-one tensors is a smooth semialgebraic manifold: its algebraic equations are the flattening minors, with the origin removed. The sum of $r$ such tensors is a polynomial map on their product. Generic complex identifiability implies that the ordered map has finite generic fibers, consisting of permutations. In characteristic zero it is unramified on a dense open set of its image. Restrict to that regular identifiable locus and to real points. The omitted algebraic or semialgebraic exceptional subset has smaller dimension and induced volume zero. This is the regular, full-measure cone used in Proposition 2.2 of the source paper. We use local inverses and do not assume a global labeling of summands.

Denote the resulting smooth semialgebraic cone by $M^\circ$. Its dimension is
\[
k=r\left(1+\sum_{j=1}^d(n_j-1)\right)>1.
\]
The dimension formula follows because the nonzero rank-one cone has the displayed summand dimension and the ordered addition map is generically finite. Let
\[
L=M^\circ\cap\{A:\|A\|=1\}.
\]
The radial direction is tangent to the cone, so the unit sphere is transverse and $L$ is smooth of dimension $s=k-1\ge1$.

Define $G$ to consist of all
\[
\left(A,\frac{a_1}{\|a_1\|},\ldots,\frac{a_r}{\|a_r\|}\right),
\quad A\in L,\quad A=\sum_i a_i,
\]
where $(a_1,\ldots,a_r)$ ranges over its ordered minimal decompositions. The set is semialgebraic: the addition, rank-one and normalization relations are polynomial equalities and inequalities after introducing positive variables $t_i$ with $t_i^2=\|a_i\|^2$ and $t_i u_i=a_i$, and then projecting away $a_i,t_i$. Identifiability can likewise be expressed by a quantified polynomial formula, or imposed by restriction to the regular identifiable semialgebraic locus above.

This graph is bounded, even though the unnormalized summands can diverge: $\|A\|=1$ and each normalized summand has norm one. Its projection fibers are finite and nonempty. No two summands in a minimal decomposition can be proportional, since they could be combined or canceled to reduce the number of terms. Consequently the $r!$ permutations yield distinct ordered normalized tuples. Near a regular point the graph consists of their smooth local branches. The derivative norms are identical under these permutations.

Apply (1) to the restriction of $f$ to the link. It follows that
\[
I_L:=\int_L\|D(f|_L)(A)\|_2\,dV_L(A)<\infty. \tag{2}
\]
This argument is unaffected by a branch permutation around a loop. It makes no claim that the ordered addition map is globally one-to-one.

## 4. Radial integration

For $t>0$, uniqueness gives $\Psi(tA)=t\Psi(A)$ locally with compatible labels. Therefore $f(tA)=f(A)$. The radial derivative vanishes. The orthogonal decomposition
\[
T_A M^\circ=\mathbb R A\oplus T_A L\qquad(A\in L)
\]
shows $\|Df(A)\|_2=\|D(f|_L)(A)\|_2$ and, at general radius,
\[
\kappa_{\rm ang}(tA)=t^{-1}\|D(f|_L)(A)\|_2. \tag{3}
\]
The polar map $(t,A)\mapsto tA$ on the cone has volume element $t^{k-1}\,dt\,dV_L(A)$. Tonelli's theorem, (2) and (3) give
\[
\int_{M^\circ}e^{-\|A\|^2/2}\kappa_{\rm ang}(A)\,dV_M(A)
= I_L\int_0^\infty t^{k-2}e^{-t^2/2}\,dt<\infty.
\]
The radial integral converges at zero because $k>1$ and at infinity because of Gaussian decay. Similarly
\[
Z=\mathcal H^{k-1}(L)\int_0^\infty t^{k-1}e^{-t^2/2}\,dt
\]
is finite and positive: $L$ is nonempty and smooth of its stated dimension and is bounded semialgebraic. Restoring the removed null set does not change these integrals. Dividing by $Z$ proves the theorem.

The proof also covers rank two under the same assumptions, consistently with the known theorem. It does not imply integrability of the ordinary condition number: the graph of the unnormalized summands need not be bounded. Nor does it prove higher moments, since a graph Jacobian need not dominate an arbitrary power of its largest singular value.

## References

1. C. Beltran, P. Breiding and N. Vannieuwenhoven, *The Average Condition Number of Most Tensor Rank Decomposition Problems Is Infinite*, Foundations of Computational Mathematics 23 (2023), 433-491. [Preprint](https://arxiv.org/abs/1903.05527), Definition 1.3, Conjecture 1.10, Proposition 2.2 and Lemma 6.1; [journal](https://doi.org/10.1007/s10208-022-09551-1), equation (6), Theorem 3 and Conjecture 2.
2. R. Hardt, P. Lambrechts, V. Turchin and I. Volic, *Real homotopy theory of semi-algebraic sets*, Algebraic & Geometric Topology 11 (2011), 2477-2545, Theorem 2.4. [Primary text](https://msp.org/agt/2011/11-5/agt-v11-n5-p01-s.pdf).
3. [Canonical TR-06 statement](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/tensor-computations/TR-06/README.md), checked 11 September 2026. The bounded search and claim inventory are recorded separately in the submission record.
