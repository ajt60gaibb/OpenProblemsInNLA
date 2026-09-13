# FR-12: A matching-indexed doubling counterexample

**George Stepaniants**  
Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA  
12 September 2026

Let $H(n)$ count labeled real Hadamard matrices of order $n$. An injective
construction gives $H(2m)\ge(2m-1)!!H(m)^2$. Iteration yields
$H(2^k)\ge 2^{2^k(k-1)(k-2)/8}$ for $k\ge2$.
Consequently no absolute constant $C$ satisfies $H(n)\le2^{Cn\log_2 n}$
at every order divisible by four. This refutes the exact counting target of
FR-12; it does not address existence at every admissible order.

**Assistance and independent review.** Prepared with substantial assistance
from Codex. A separate Codex agent independently audited the complete
supplied argument and reported PASS on 12 September 2026. The
[signed independent review](../../references/stepaniants-fr12-2026-09-12/REVIEW.md)
identifies the exact archived source and scope. This is an informal AI-agent
audit, not external human peer review or formal verification. The
supplementary finite checker is not a universal proof certificate, and no
historical priority certification is claimed.

## Exact target

Write

$$
 \mathcal H_n=\{A\in\{-1,1\}^{n\times n}:AA^{\mathsf T}=nI_n\},
 \qquad H(n)=|\mathcal H_n|.
$$

Rows and columns are labeled; signed permutations are *not* quotiented
out. The target in FR-12 [2], attributed to
Ferber--Jain--Zhao [1], is whether an absolute $C>0$ gives

$$
 H(n)\le 2^{Cn\log_2 n}\qquad(4\mid n).
 \tag{1}
$$

We count actual matrices, so no assumption about automorphism groups or
sizes of equivalence classes enters the argument.

**Lemma 1 (Injective doubling).** For every positive integer $m$,

$$
 H(2m)\ge \frac{(2m)!}{2^m m!}\,H(m)^2=(2m-1)!!\,H(m)^2.
 \tag{2}
$$

**Proof.** Let $\mathfrak M_{2m}$ denote the perfect matchings of the labeled positions
$\{1,\ldots,2m\}$. Given a matching, write each pair as $(u_i,v_i)$ with
$u_i<v_i$, and order its pairs by $u_1<\cdots<u_m$.
For $A,B\in\mathcal H_m$, define a $2m\times2m$ sign matrix $C$ by

$$
 C_{u_i,\cdot}=(A_{i,\cdot},B_{i,\cdot}),\qquad
 C_{v_i,\cdot}=(A_{i,\cdot},-B_{i,\cdot}),\quad 1\le i\le m.
 \tag{3}
$$

Each row has squared norm $2m$. The inner product of the two rows in one
pair is $m-m=0$. For two different pairs $i\ne j$, all four possible inner
products vanish, since they have the form

$$
 \langle A_{i,\cdot},A_{j,\cdot}\rangle
 \mathbin{\pm}\langle B_{i,\cdot},B_{j,\cdot}\rangle=0.
$$

Thus $C\in\mathcal H_{2m}$.

The map $(A,B,\mathcal M)\mapsto C$ is injective. Indeed, distinct rows of
$A$ are distinct vectors: equality of two rows would contradict their
orthogonality. It follows that, among the rows of $C$, equality of the
*first $m$ coordinates* partitions the $2m$ row positions into exactly
the pairs of $\mathcal M$. Hence $C$ recovers the matching. Its canonical
pair ordering then recovers $A$ from these first halves. For each pair,
the last $m$ coordinates of the smaller-indexed row recover the corresponding
row of $B$. This also fixes every sign, so no residual multiplicity remains.

Finally, $|\mathfrak M_{2m}|=(2m)!/(2^m m!)$: list all positions in an order,
pair successive positions, and divide by the $2^m$ orders within pairs and
the $m!$ orders of the pairs. Counting the domain of the injection proves
(2). ∎

**Theorem 1 (A super-$n\log n$ exponent).** For every integer $k\ge2$,

$$
 \boxed{H(2^k)\ge 2^{\,2^k(k-1)(k-2)/8}.}
 \tag{4}
$$

In particular, assertion (1) is false.

**Proof.** Hadamard matrices exist at every power of two, by applying
(3) recursively starting with an order-one sign matrix.
Consequently the logarithms below are defined. Put

$$
 a_k=2^{-k}\log_2 H(2^k).
$$

For $k\ge2$, let $m=2^{k-1}$, so $m$ is even. The matching factor satisfies

$$
 (2m-1)!!=\prod_{j=1}^m(2j-1)\ge m!
 \ge (m/2)^{m/2}.
$$

The last inequality retains just the largest $m/2$ factors in $m!$ and
bounds each from below by $m/2$. Taking logarithms of
(2) and dividing by $2m$ gives

$$
 a_k\ge a_{k-1}+\frac{\log_2m-1}{4}
       =a_{k-1}+\frac{k-2}{4}.
$$

Since $a_1\ge0$, summation yields

$$
 a_k\ge\frac14\sum_{j=2}^k(j-2)
      =\frac{(k-1)(k-2)}8,
$$

which proves (4).
If (1) held, applying it at $n=2^k$ would give $a_k\le Ck$.
This contradicts the displayed quadratic lower bound for sufficiently large
$k$. All these $n$ are divisible by four. ∎

## Checks, attribution, and scope

The supplementary script checks the equivalent row-permutation formulation:
form $\left(\begin{smallmatrix}A&B\\A&-B\end{smallmatrix}\right)$, then
permute its $2m$ rows. Every output has exactly $2^m m!$ preimages in that
formulation. The matching-indexed construction in Lemma 1
removes this multiplicity explicitly.

| $m$ | $H(m)$ | Input triples | Distinct outputs | Fiber size |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 2 | 8 | 4 | 2 |
| 2 | 8 | 1536 | 192 | 8 |

Those finite cases, and exact integer checks of the iterated lower bound
through $k=10$, are not used to infer an asymptotic statement. The analytic
injection and its iteration establish the result for every $k$.

The construction uses only power-of-two orders. It neither resolves the
Hadamard existence conjecture nor supplies a matching upper bound on $H(n)$.
The original counting question and the published upper bounds remain
attributed to their sources. The accompanying audit states the observed
public branch scope and the limits of the duplicate/literature search.

## References

1. A. Ferber, V. Jain, and Y. Zhao,
   *On the number of Hadamard matrices via anti-concentration*,
   Combinatorics, Probability and Computing 31 (2022), 455--477.
   [doi:10.1017/S0963548321000377](https://doi.org/10.1017/S0963548321000377).
   Published Conjecture 1.3; Conjecture 1.4 in
   [arXiv:1808.07222v1](https://arxiv.org/abs/1808.07222).
2. *Open Problems in Numerical Linear Algebra*, entry FR-12,
   `ajt60gaibb/OpenProblemsInNLA`, snapshot
   `1f22006bdaa4659fcaa0bb775a887685cd3cc566`.
   [Retained canonical target](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/1f22006bdaa4659fcaa0bb775a887685cd3cc566/frames-and-matrix-designs/FR-12/README.md).
