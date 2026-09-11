# Audit of the random-graph inputs to MD-06

This note spells out the model conversion and fixed-parameter counting behind the main manuscript. It is supplementary to the cited theorems, not independent peer review. All graph sizes tend to infinity through even integers.

## 1. Why the configuration model conditions to the desired distribution

Give each labelled vertex three labelled half-edges and choose a uniform perfect matching of the \(3n\) half-edges. Every pairing has the same probability. A prescribed collection of \(e\) disjoint half-edge pairs occurs with probability

\[
\frac1{(3n-1)(3n-3)\cdots(3n-2e+1)}.
\]

For fixed \(e\), this is \(O(n^{-e})\). Every labelled simple cubic graph is represented by exactly \((3!)^n\) pairings: at each vertex its three half-edges may be assigned bijectively to its three distinct incident edges. Thus conditioning the pairing model on simplicity gives the uniform labelled **simple** cubic graph, not an unlabeled or differently weighted model.

Let \(C_1\) count loops, \(C_2\) count unordered pairs of parallel edges, and \(C_k\), \(k\ge3\), count simple cycles with their usual unoriented convention. The pairing is simple if and only if \(C_1=C_2=0\). Triple edges are excluded by this condition too, because they contain pairs of parallel edges.

## 2. Fixed cycle counts and simplicity

For a fixed \(k\ge3\), direct counting gives

\[
\mathbb EC_k
=\frac{(n)_k6^k}{2k}
\frac1{(3n-1)(3n-3)\cdots(3n-2k+1)}
\longrightarrow\frac{2^k}{2k}.
\]

The factor \((n)_k/(2k)\) counts ordered distinct vertices up to rotation and reversal. Each vertex uses an ordered pair of distinct half-edges, giving \(3\cdot2=6\) choices. The same limiting means for loops and double edges are \(\mu_1=1\) and \(\mu_2=1\), obtained by direct half-edge choices.

For any fixed collection of factorial moments of \(C_1,\ldots,C_r\), the leading contribution consists of vertex-disjoint cycles. Its limit is the product of the corresponding powers of

\[
\mu_k=\frac{2^k}{2k}.
\]

All overlapping contributions are \(O(1/n)\). To see this, take the union of a fixed ordered tuple of distinct cycles. Any component containing more than one cycle has excess \(e-v\ge1\); other components have excess zero. There are only finitely many resulting bounded half-edge patterns for a fixed moment. An embedding supplies at most \(O(n^v)\) choices and its prescribed pairs have probability \(O(n^{-e})\). Distinct cycles are enforced by falling factorials, so merely choosing the same cycle twice is not an overlapping contribution that has been omitted.

The factorial-moment argument yields joint convergence to independent Poisson variables. This is the usual fixed-length Poisson law, and it is also available directly for the uniform simple model in Johnson's Theorem 11. In particular,

\[
\Pr(C_1=C_2=0)\longrightarrow e^{-2}>0.
\]

Since the limiting Poisson variables are independent, conditioning on \(C_1=C_2=0\) leaves the limiting law of \(C_k\), \(k\ge3\), unchanged. Point probabilities can be passed to the limit here because the variables are integer-valued; equivalently, use half-integer continuity boxes. Thus in the required simple model,

\[
C_k\Rightarrow\operatorname{Poisson}(2^k/(2k))
\]

for every **fixed** \(k\). No assertion about cycle lengths growing with \(n\) is needed.

## 3. Bounded subgraphs and clean neighborhoods

For any fixed simple graph \(H\) of maximum degree at most three, with \(v\) vertices and \(e\) edges, there are at most \(n^v\) vertex embeddings and a bounded number of compatible half-edge assignments per embedding. The expected number of embedded copies in the pairing model is therefore \(O_H(n^{v-e})\). Conditioning on simplicity multiplies this by at most a fixed constant for all sufficiently large \(n\), because the conditioning probability tends to \(e^{-2}\).

If \(e\ge v+1\), the probability of any copy is \(O_H(1/n)\). This elementary fixed-size argument agrees with the direct simple-model estimate in Johnson's Proposition 1(a). The main manuscript uses that proposition and therefore does not depend on repeating the configuration-model derivation.

The radius-\(R\) neighborhood of a fixed-length \(\ell\)-cycle in a cubic graph has at most \(\ell2^R\) vertices. If it contains a second independent cycle, pruning leaves produces a bounded nonempty graph with minimum degree at least two and \(e-v\ge1\). There are finitely many possible types for fixed \(\ell,R\), so the probability of any dirty neighborhood is \(O_{\ell,R}(1/n)\).

Likewise, two distinct fixed-length cycles at distance at most \(2R\) supply a bounded bicyclic subgraph, after including a shortest connecting path. This proves the separation estimate used in `md06_many_minima.md`.

## 4. The spectral input and its constant

Bordenave's Theorem 1 applies to the uniform labelled simple \(d\)-regular graph. For each fixed \(d\ge3\) and \(\varepsilon>0\), its nontrivial adjacency eigenvalues have absolute value at most \(2\sqrt{d-1}+\varepsilon\) with probability tending to one. Set \(d=3\) and choose, for example, \(\varepsilon=1/20\). Then

\[
\lambda_2(L_{G_n})
\ge3-2\sqrt2-1/20>1/10
\]

on that event. The last inequality is elementary; \(2\sqrt2<57/20\) suffices. The event implies connectedness: a disconnected regular graph has a second adjacency eigenvalue equal to three.

A fixed positive spectral gap, not the sharp Ramanujan-scale value, is all the existence argument needs. The particular value \(1/10\) is used to state the convenient uniform Hessian margin \(1/320\). The proof does not require an explicit convergence rate in the spectral theorem.

## 5. Quantifier audit

For each selected cycle length, the radius is chosen once and held fixed throughout the \(n\)-limit. To prove the probability-one existence assertion, one first obtains a limit-superior bound for every fixed multiple of four and only then lets that multiple grow. For the multiplicity consequence, the desired number of gadgets is fixed as well. Consequently, none of the arguments silently require uniform Poisson approximation, tangle estimates, or spectral convergence for a parameter growing with \(n\).

Primary references and exact model locators: Bordenave, arXiv:1502.04482v4, Theorem 1, printed page 2; Johnson, arXiv:1112.0704v5, Section 2 and Proposition 1(a), printed page 3, and Theorem 11, printed page 12. See `SOURCES.md` for links.
