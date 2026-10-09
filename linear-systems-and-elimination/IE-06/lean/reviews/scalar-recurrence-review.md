# Scalar recursion specification and review

The source-analysis agent proposed this exact restricted intermediate route before coding. The root coordinator and the independent mathematical reviewer approved it on 2026-10-06. It preserves the full SchurSubpolynomialTail target; it does not claim the manuscript's stronger arbitrary-r logarithm-of-logarithm estimate.

Let $\ell>0$, let $d\ge1$ be an integer, and set

$$
k_\ell(d)=\max(100d,\lceil d^2/\ell\rceil),\qquad
d_i=k_\ell^{[i]}(d).
$$

The formal finite stopped cost is

$$
h_{n,\ell}(d)=\sum_{i=0}^{n-1}
 \mathbf1_{\{d_i<n\}}(1+\ell/d_i).
$$

The source's infinite-index stopped sum equals this finite sum because $d_i\ge d+i$, hence $d_n\ge n$. No discarded index can contribute.

The approved contracts, now implemented in NLA/IE06/ScalarRecurrence.lean, are:

- The step and every iterate are monotone in the starting integer.
- $d_i\ge100^id$, $d_i\ge d+i$, and the chain terminates by index $n$.
- $h(d)=0$ if $d\ge n$.
- For $0<d<n$, $h(d)=1+\ell/d+h(k_\ell(d))$.
- The cost is antitone on positive starting integers.
- For every finite $m$, $\sum_{i<m}\ell/d_i\le2\ell/d$.
- If $d_m\ge n$, at most $m$ terms contribute and $h(d)\le m+2\ell/d$.
- For $\ell=\log n\ge256$ and $J=\lceil\sqrt\ell\rceil$, every $d\ge J$ reaches $n$ by index $2J$, and $h(d)\le6\sqrt\ell$.
- $k_\ell(d)\le d^2/\ell+100d$, and $1+k_\ell(d)\ell/d^2\le2+100\ell/d$.
- For the source threshold $g(d)=(d/\sqrt n)\exp(-D h(d))$, positivity holds when $n,d>0$; $g(d)/d$ is nondecreasing for $D\ge0$; and the exact one-step multiplicative recurrence holds.

The cost proof uses two blocks of $J$ steps. First, $100^J\ge100J$ and $J^2\ge\ell$ imply $d_J\ge100\ell$. Quadratic growth then gives $d_{2J}\ge\ell100^{2^J}\ge e^\ell=n$, using $J\ge16$, $2^J\ge J^2$, and $\log100\ge1$. There are at most $2J$ contributions, so $h(d)\le2J+2\ell/d\le6\sqrt\ell$.

All constants and inequalities are exact. The imported bound $\exp(1)<3$ establishes $\log100\ge1$ without numerical sampling or large dimension evaluation. The module uses no Gaussian/random-matrix hypotheses and proves no Gaussian tail by itself.

Every definition and theorem in this module has its own LeanCert kernel trust assertion and printed transitive axioms. The local compilation succeeded with only propext, Classical.choice and Quot.sound. Independent code review and the final whole-project clean-snapshot verification are recorded separately when completed.
