# Algebraic complexity and matrix powering

These problems concern the arithmetic cost of matrix computations and the tensor
representations underlying fast algorithms. All status checks below were made
on **2026-09-08**. An unsuccessful search for a resolution is not proof that
none exists. Ratings are editorial.

<a id="ac-01"></a>

## AC-01 — Is the matrix multiplication exponent two?

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Topic:** arithmetic complexity of dense matrix multiplication

**Statement.** Over the field $\mathbb C$, let $M(n)$ be the minimum number of
scalar additions, subtractions, multiplications, and divisions in an arithmetic
straight-line program computing every entry of $AB$ for arbitrary
$A,B\in\mathbb C^{n\times n}$. Programs must be defined on their intended inputs.
Set $\omega=\inf\{\tau:M(n)=O(n^\tau)\}$. Is $\omega=2$? Equivalently, for every
$\varepsilon>0$, can these products be computed in $O(n^{2+\varepsilon})$
arithmetic operations? This asks about asymptotic arithmetic cost; it does not
assert an $O(n^2)$ algorithm or a floating-point stability guarantee.

**Why it matters.** Matrix multiplication is a basic cost driver for dense NLA.

**References and status.** M. Bläser, [*Fast Matrix Multiplication*](https://theoryofcomputing.org/articles/gs005/gs005.pdf),
Graduate Surveys 5 (2013), §§1, 5, provides the computational model. E. Dupont
et al., [*Improving the matrix multiplication exponent with modern optimization
and AlphaEvolve*](https://arxiv.org/abs/2608.16884) (2026), abstract and §1,
reports $\omega<2.371177$, which does not reach two. Searches for “matrix
multiplication exponent 2026” and “omega equals 2 proof” located improvements,
not a resolution. **Admitted: no resolution located.**

<a id="ac-02"></a>

## AC-02 — Exact bilinear rank of the $3\times3$ matrix product

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Topic:** small matrix multiplication algorithms

**Statement.** Determine the least integer $r$ for which there are complex
coefficients $u_{t,ij},v_{t,ij},w_{ij,t}$ satisfying, for every pair of complex
$3\times3$ matrices,

$$
(AB)_{ij}=\sum_{t=1}^{r} w_{ij,t}
 \left(\sum_{a,b=1}^{3}u_{t,ab}A_{ab}\right)
 \left(\sum_{c,d=1}^{3}v_{t,cd}B_{cd}\right).
$$

Scalar linear combinations are free in this bilinear-rank model. The classical
upper bound is 23; deciding whether 22 products suffice is part of determining
the exact minimum. Algorithms mixing entries of both inputs within a factor
are outside this specified model.

**Why it matters.** Such identities can be applied recursively to matrix blocks.

**References and status.** Bläser, [2013](https://theoryofcomputing.org/articles/gs005/gs005.pdf),
§1 and Example 5.10. Y. Sun, [*An Exact 56-Addition, Rank-23 Scheme for General
3×3 Matrix Multiplication*](https://arxiv.org/abs/2604.27645) (2026), gives another
23-product scheme. C. Wang, [*Automated Lower Bounds for Bilinear Complexity
over Finite Fields*](https://arxiv.org/abs/2603.07280), v10 (2026), improves a
lower bound over $\mathbb F_2$; that is not a complex-field resolution. Searches
for “rank 22 matrix multiplication 2026 proof” found no qualifying algorithm
or matching lower bound. **Admitted: no resolution located.**

<a id="ac-03"></a>

## AC-03 — Border rank of the $3\times3$ matrix product

**Difficulty:** extreme  
**Importance:** interesting to the community  
**Topic:** approximate bilinear algorithms

**Statement.** In $\mathbb C^9\otimes\mathbb C^9\otimes\mathbb C^9$, let

$$M_3=\sum_{i,j,k=1}^{3}e_{ij}\otimes e_{jk}\otimes e_{ki}.$$

The tensor rank $R(T)$ is the minimum number of pure tensors in an exact sum
for $T$. The border rank $\underline R(T)$ is the least $r$ such that $T$ is a
Euclidean limit of tensors of rank at most $r$. Determine
$\underline R(M_3)$. The use of limits makes this a different invariant from
AC-02.

**Why it matters.** Degenerating bilinear algorithms underlie asymptotic
improvements in matrix multiplication.

**References and status.** A. Conner, A. Harper, J. M. Landsberg,
[*New lower bounds for matrix multiplication and det₃*](https://arxiv.org/abs/1911.07981),
Theorem 1.1, proves $\underline R(M_3)\ge17$. J. Alman and B. Li,
[*Asymptotic Rank Speedup Theorems, Revisited*](https://arxiv.org/abs/2605.21738)
(2026), §1, explicitly identifies this exact border rank as open. Searches for
“3x3 border rank matrix multiplication 2026” found no exact determination.
**Admitted: no resolution located.**

<a id="ac-04"></a>

## AC-04 — Minimal asymptotic rank of the small Coppersmith–Winograd tensor

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Topic:** asymptotic tensor algorithms

**Statement.** Let $e_0,e_1,e_2$ be the standard basis of $\mathbb C^3$ and set

$$T=\sum_{i=1}^{2}(e_0\otimes e_i\otimes e_i+
 e_i\otimes e_0\otimes e_i+e_i\otimes e_i\otimes e_0).$$

For a tensor $S$, define $\widetilde R(S)=\lim_{k\to\infty}
R(S^{\otimes k})^{1/k}$, grouping corresponding factors when taking powers.
Is $\widetilde R(T)=3$?

**Why it matters.** This explicitly studied tensor offers a route to exponent
two for matrix multiplication. It is not counted separately for other values
of its size parameter.

**References and status.** Bläser, [2013](https://theoryofcomputing.org/articles/gs005/gs005.pdf),
Problem 9.8. Alman–Li, [2026](https://arxiv.org/abs/2605.21738),
Theorems 1.2–1.3, relates the target to $\omega=2$ and establishes the partial
upper bound $\widetilde R(T)<3.931$. Searches for “small Coppersmith Winograd
asymptotic rank 2026 3” located that improvement, not equality. Border-rank
results for a fixed tensor power do not alone determine this limit.
**Admitted: no resolution located.**

<a id="ac-05"></a>

## AC-05 — Strassen's asymptotic rank conjecture for tight tensors

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Topic:** complexity of structured tensor powers

**Statement.** A tensor $T\in(\mathbb C^d)^{\otimes3}$ is *concise* if each of its
three matrix flattenings has rank $d$. It is *tight* if some choice of bases
admits injective functions $a,b,c:\{1,\ldots,d\}\to\mathbb Z$ with
$a(i)+b(j)+c(k)=0$ whenever the coefficient $T_{ijk}$ is nonzero. Is

$$\lim_{m\to\infty}R(T^{\otimes m})^{1/m}=d$$

for every positive integer $d$ and every concise tight $T$? Tensor powers use
corresponding-factor grouping; rank is over $\mathbb C$.

**Why it matters.** This is a structural conjecture about many bilinear
computations, beyond the single matrix-multiplication family. AC-04 is a named special tensor
with independent literature treatment; this universal statement is not its
equivalent reformulation.

**References and status.** A. Björklund and P. Kaski,
[*The Asymptotic Rank Conjecture and the Set Cover Conjecture are not Both
True*](https://arxiv.org/abs/2310.11926), Conjecture 3 and §2.3, states the
conjecture and gives a conditional consequence, not a refutation. K. Lee,
[*Asymptotic rank bounds: a numerical census*](https://arxiv.org/abs/2601.08119)
(2026), Conjecture 1, retains the tight/concise formulation. Searches for
“asymptotic rank conjecture proved 2026” found no resolution. Numerical evidence
is not a proof. **Admitted: no resolution located.**

<a id="ac-06"></a>

## AC-06 — Explicit tensors with quadratic border rank

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Topic:** explicit lower bounds for tensor decompositions

**Statement.** Construct a deterministic algorithm that, on input the positive
integer $n$, outputs the rational entries of a tensor
$T_n\in\mathbb Q^{n\times n\times n}$ in time polynomial in $n$, and prove that
there are constants $c>0,n_0$ such that
$\underline R_{\mathbb C}(T_n)\ge c n^2$ for all $n\ge n_0$.
Output rationals are encoded by binary integer numerators and denominators;
thus the time bound also limits their bit lengths. Border rank is defined as
in AC-03.

**Why it matters.** Explicit hard tensors would supply lower bounds for
bilinear computation that are much stronger than the currently available
examples. Generic existence does not provide the required efficient construction.

**References and status.** M. Michałek and J. Landsberg,
[*Towards Finding Hay in a Haystack: Explicit Tensors of Border Rank Greater
Than 2.02m*](https://www.theoryofcomputing.org/articles/v021a013/v021a013.pdf),
Theory of Computing 21(13), 2025, §1 and Definition 1.1, distinguishes
polynomial-time explicitness from weaker notions and obtains a linear bound.
The quadratic target and rational-output encoding are an editorial quantitative
formulation of the paper's explicit-versus-generic challenge, not a numbered
conjecture quoted from it. Searches for “explicit tensors
superlinear rank 2026” and “explicit tensors superlinear border rank” located
no quadratic construction; weaker semi-explicit constructions do not meet this
statement. **Admitted: no resolution located.**

<a id="ac-07"></a>

## AC-07 — Scholz–Brauer inequality for multiplication chains

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Topic:** multiplication counts for matrix powers

**Statement.** An addition chain for a positive integer $n$ is a sequence
$1=a_0<a_1<\cdots<a_r=n$ in which every $a_i$ with $i>0$ is a sum of two earlier
terms, which may coincide. Let $\ell(n)$ be its minimum possible length $r$.
Is

$$\ell(2^n-1)\le n+\ell(n)-1\qquad(n\ge1)?$$

The case $n=1$ uses $\ell(1)=0$. A chain implements a computation of $A^n$ by
matrix multiplications; the question is about this multiplication-only model,
not every possible matrix-function algorithm.

**References and status.** Bläser, [2013](https://theoryofcomputing.org/articles/gs005/gs005.pdf),
Research Problem 2.9. N. Clift, [*A Short Note on Exact Equality for the
Scholz–Brauer Conjecture*](https://www.additionchains.com/ExactScholzBrauer.pdf)
(2024), distinguishes this inequality from the stronger equality and gives a
counterexample to equality. T. Agama,
[*A Progress on the Scholz Conjecture on Addition Chains*](https://www.researchgate.net/publication/397490267_A_PROGRESS_ON_THE_SCHOLZ_CONJECTURE_ON_ADDITION_CHAINS),
manuscript dated 10 May 2026, §1, still states the general inequality as open;
its result imposes additional conditions on an optimal addition chain.
Searches for “Scholz Brauer conjecture proof 2026” and inspection of these
sources found no proof or disproof of the unrestricted inequality.
**Admitted: no resolution located.**

<a id="ac-08"></a>

## AC-08 — Knuth–Stolarsky lower bound for addition chains

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Topic:** lower bounds for multiplication-only powering

**Statement.** With $\ell(n)$ defined in AC-07, let $\nu(n)$ be the number of
ones in the binary expansion of a positive integer $n$. Is

$$\ell(n)\ge \lfloor\log_2 n\rfloor+
 \lceil\log_2\nu(n)\rceil\qquad(n\ge1)?$$

These rounding conventions are part of the statement. This would constrain
multiplication chains for $A^n$ and complements the upper bound in AC-07.

**References and status.** E. G. Thurber,
[*The Scholz–Brauer problem on addition chains*](https://msp.org/pjm/1973/49-1/pjm-v49-n1-p25-s.pdf),
Pacific Journal of Mathematics 49 (1973), p. 229, states the equivalent
small-step conjecture and treats a restricted case. H. Altman,
[*Internal structure of addition chains: Well-ordering*](https://www.sciencedirect.com/science/article/am/pii/S0304397517308666)
(2018), Conjecture 1.7 and §4, distinguishes proved cases from the general claim.
Searches for “Knuth Stolarsky conjecture 2026 proof” found no general resolution.
Bläser's Research Problem 2.10 is a discovery lead; this entry uses the explicit
floor/ceiling formulation in the specialized sources. **Admitted: no resolution
located.**

## Screened out — not part of the open count

- **Direct-sum additivity of tensor rank:** Bläser's Research Problem 5.7 is
  historical. Y. Shitov, [*A counterexample to Strassen's direct sum
  conjecture*](https://arxiv.org/abs/1712.08660), disproves it. Do not confuse it
  with the asymptotic-rank conjecture.
- **An unrestricted complexity classification for tensor rank over a field:**
  Bläser's Problem 5.11 has a later classification by M. Schaefer and D.
  Štefankovič, [*The Complexity of Tensor Rank*](https://arxiv.org/abs/1612.04338).
  Remaining decidability questions over $\mathbb Q$ require a separate,
  accurately sourced formulation; this old question is not counted unchanged.
- **Strict improvement over the border-rank upper bound for the small
  Coppersmith–Winograd tensor:** the specific remaining target is AC-04;
  merely obtaining a bound below four is already achieved by Alman–Li.
