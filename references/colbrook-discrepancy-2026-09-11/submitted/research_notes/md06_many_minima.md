# MD-06: a supplementary multiplicity consequence

**Status:** a further consequence of the same proof claim, pending independent review. This is not a second solved repository problem. The statement below does not assert a rate of growth in the number of vertices.

Let \(N(G)\) be the number of distinct nonsynchronized local minima of the Kuramoto energy, modulo common phase rotation, whose Hessian is positive definite on the mean-zero subspace. The proof counts explicitly separated minima and does not require that all critical points of the graph be isolated.

## Deterministic statement

Suppose a connected simple cubic graph has unweighted Laplacian gap at least \(\gamma>0\). Suppose it contains \(m\) cycles \(C_1,\ldots,C_m\), each of the same length \(\ell\in4\mathbb N\), whose radius-\(R\) neighborhoods are clean and pairwise vertex-disjoint. Put \(c=1/16\). If \(R\ge4\) and

\[
2^{R-1}>\frac{32m\ell}{c^4\gamma^2},
\]

then

\[
N(G)\ge2^m-1.
\]

Each counted minimum has edge cosines at least \(1/32\) and mean-zero Hessian at least \((\gamma/32)I\).

### Proof

For each cycle use the signed binary-tree profile from Proposition 6 of the main manuscript, denoted by \(\phi^{(i)}\). Its nonzero coordinates lie strictly inside its radius-\(R\) neighborhood. Its gradient is supported only on the depth-\(R\) boundary. The cosine margin is at least \(c_0>1/16=c\), and

\[
\|\nabla E_G(\phi^{(i)})\|_2^2
=\ell t_R^2 2^{1-R}.
\]

For every subset \(A\subseteq\{1,\ldots,m\}\), set

\[
\phi^A=\sum_{i\in A}\phi^{(i)}.
\]

No edge joins two nonzero supports. Indeed, a neighbor of a vertex at depth less than \(R\) belongs to that cycle's radius-\(R\) neighborhood; an edge into another nonzero support would make the neighborhoods intersect. Similarly, a boundary vertex cannot be adjacent to nonzero supports from two different neighborhoods. Consequently, the gradient contributions for different active cycles have disjoint supports, and every edge difference is either a single-profile difference or zero. Thus

\[
\min_{e\in E}\cos(\phi^A_u-\phi^A_v)\ge c,
\qquad
\|\nabla E_G(\phi^A)\|_2^2
=|A|\ell t_R^2 2^{1-R}
\le m\ell t_R^2 2^{1-R}.
\]

The small-gradient lemma applies to every subset simultaneously as a deterministic existence statement. It gives an exact local minimum \(\theta^A\) whose correction changes each edge difference by less than \(c/2=1/32\). The empty subset may be assigned the exactly synchronized vector zero.

To prove distinctness, choose a cross-sign core edge on each cycle. If \(i\in A\), the original distance of that edge difference from \(2\pi\mathbb Z\) is \(\delta_0>\pi/6>1/2\); after correction the distance is greater than \(15/32\). If \(i\notin A\), both original endpoint phases are zero, and after correction that distance is less than \(1/32\). The edge differences therefore recover the membership of every \(i\) in \(A\). They are unchanged by a common phase rotation, so minima from different subsets are distinct even after quotienting by rotation. Every nonempty subset is nonsynchronized. This proves the count and the stability bounds.

## Consequence for uniform random cubic graphs

For every fixed positive integer \(m\),

\[
\Pr\bigl(N(G_n)\ge2^m-1\bigr)\longrightarrow1.
\]

Equivalently, the number of such nonsynchronized local minima diverges in probability. The same assertion holds when the counted minima are required to have all edge cosines at least \(1/32\) and mean-zero Hessian at least \((1/320)I\).

### Proof and order of limits

Fix \(m\), a multiple of four \(\ell\), and a radius \(R\) satisfying the deterministic bound with \(\gamma=1/10\). All these parameters remain fixed as \(n\to\infty\).

The spectral gap event has probability tending to one by the same Bordenave/Friedman input as the main manuscript. The probability of any nonclean \(\ell\)-cycle neighborhood is \(O_{\ell,R}(1/n)\).

The probability that two distinct \(\ell\)-cycles have intersecting radius-\(R\) neighborhoods is also \(O_{\ell,R}(1/n)\). Such cycles are joined by a path of length at most \(2R\), or already intersect. Their union, with a connecting path when needed, contains a bounded graph of minimum degree at least two and excess \(e-v\ge1\). The fixed-subgraph bound and embedding count used in the main manuscript apply again. This is a bound for fixed parameters and does not claim uniformity in growing \(m,\ell,R\).

The number of \(\ell\)-cycles converges to a Poisson variable of mean \(\mu_\ell=2^\ell/(2\ell)\). Hence

\[
\limsup_n\Pr\bigl(N(G_n)<2^m-1\bigr)
\le
\Pr\bigl(\operatorname{Poisson}(\mu_\ell)<m\bigr).
\]

This holds for each fixed multiple of four \(\ell\). Letting \(\ell\) tend to infinity **after** the limit superior makes the right side zero. No independence of expansion, cleanliness, separation, or cycle counts is required.

## Scope

This argument gives arbitrarily many minima with high probability, but it does not give a polynomial or exponential lower bound in \(n\). The deterministic \(2^m\) count is exponential in the number of available separated gadgets, not an asserted linear-in-\(n\) supply of those gadgets. It also makes no statement about the measure of their attraction basins under randomly initialized dynamics.

The random-graph references are exactly those in the main manuscript and `SOURCES.md`: Bordenave, arXiv:1502.04482v4, Theorem 1; Johnson, arXiv:1112.0704v5, Proposition 1(a) and Theorem 11. The profile, correction lemma, and explicit constant are proved in the main manuscript. This derivation is a self-audit within the same work, not independent external verification.
