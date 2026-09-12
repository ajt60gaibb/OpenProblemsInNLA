# KE-02 — deterministic separation on two explicit tridiagonal classes

**Author:** Sidney Holden  
**Affiliation:** Center for Computational Biology, Flatiron Institute, Simons Foundation.  
**Submission date:** 12 September 2026.  
**Editorial record:** [Attribution, independent review and scope](../README.md).

The review statements below describe the supplied draft; the linked submission record records subsequent independent review.

**Classification: NEW PARTIAL RESULT.** This includes a strengthened subcase
derived during the present audit. Complete proofs are supplied for the stated
subclasses; this is **not a complete proof candidate for the original target**.
No independent review, formal verification, novelty or acceptance is asserted.

## 1. Exact repository target

For a Hermitian matrix H, with eigenvalues counted with multiplicity, let


```math
\mathop{\mathrm{gap}}\nolimits(H)=\min_{i\ne j}|\lambda_i(H)-\lambda_j(H)|.
```


The target asks for universal constants a,c_0,C,q>0 and a deterministic algorithm
which, for every n>=2, Hermitian tridiagonal T in C^{n x n} with ||T||_2<=1,
and 0<delta<1/2, receives the three diagonals and returns a **real diagonal** D
satisfying


```math
\|D\|_2\le\delta,\qquad
\mathop{\mathrm{gap}}\nolimits(T+D)\ge c_0(\delta/n)^a,
```


in at most C n[1+log(n/delta)]^q exact arithmetic operations and comparisons.
Square roots of nonnegative reals cost one operation; extracting bits from exact
real inputs is not permitted. Norms are Euclidean/operator norms throughout.

Source: canonical KE-02 README at commit
`f41f1f9ffa2171550d4bb795862c6170c4f26070`; see `../sources/snapshot.json`.
The target is not a mere existence assertion and does not allow a dense or
nondiagonal replacement perturbation.

## 2. A self-contained eigenvalue perturbation fact

If R=R* has zero diagonal, define eta=max_i sum_{j!=i}|R_ij|. For any complex x,


```math
|x^*Rx|\le\sum_{i< j}2|R_{ij}|\,|x_i|\,|x_j|
\le\sum_{i< j}|R_{ij}|(|x_i|^2+|x_j|^2)
\le\eta\|x\|^2.
```


Thus -eta I <= R <= eta I in the quadratic-form order, and ||R||_2<=eta.
If the eigenvalues of a Hermitian H are increasingly ordered, then


```math
|\lambda_j(H+R)-\lambda_j(H)|\le\eta.                 \tag{1}
```


For completeness, the variational formula used here is


```math
\lambda_j(H)=\min_{\dim L=j}\max_{x\in L,\|x\|=1}x^*Hx.
```


The span of the first j orthonormal eigenvectors gives the upper bound. Every
j-dimensional L intersects the span of the last n-j+1 eigenvectors, giving the
lower bound. Applying the quadratic-form inequalities inside this formula proves
(1). This requires only the finite-dimensional Hermitian spectral theorem.

## 3. Weak-coupling subclass, all dimensions

Write T=diag(t_1,...,t_n)+R, and define eta as above.

### Theorem A

Whenever eta<=delta/[2(n-1)], a deterministic O(n log n) algorithm produces a
real diagonal D with ||D||_2<=delta and


```math
\mathop{\mathrm{gap}}\nolimits(T+D)\ge\delta/(n-1)\ge\delta/n.    \tag{2}
```


For tridiagonal inputs, eta is computable in O(n) permitted operations.

**Proof.** Sort the real diagonal entries using a comparison sort, retaining
original indices: t_{pi(1)}<=...<=t_{pi(n)}. Put


```math
\gamma=\frac{2\delta}{n-1},\qquad
D_{\pi(j),\pi(j)}=-\delta+(j-1)\gamma.
```


Every displacement lies in [-delta,delta]. The numbers


```math
y_j=t_{\pi(j)}-\delta+(j-1)\gamma
```


are increasingly ordered and y_{j+1}-y_j>=gamma. Applying (1) to their diagonal
matrix plus R yields every adjacent eigenvalue gap at least


```math
\gamma-2\eta\ge\delta/(n-1)>0.
```


Nonadjacent differences are sums of adjacent differences. The sorting is only
internal: D is returned in the original order, so tridiagonality is preserved.
One obtains each complex off-diagonal magnitude as
sqrt(T_{i,i+1}T_{i+1,i}), a square root of a nonnegative real. Mergesort uses
O(n log n) comparisons without inspecting input bits. All remaining work is
O(n). This proves the theorem. QED.

The prior manuscript used a greedy packing recursion instead of the arithmetic
ramp. Both are valid; the ramp simplifies the audit. Within this subclass the
canonical constants may be chosen a=1, c_0=1, q=1, with a sufficiently large
universal C. Neither this proof nor its computational model introduces any
condition on bit lengths.

## 4. A second subclass with no weak-coupling restriction

Let $`\mathcal T_n`$ consist of Hermitian tridiagonal matrices with a constant
real diagonal tau and a common off-diagonal magnitude r>=0:


```math
T_{jj}=\tau,\qquad T_{j,j+1}=b_j,\qquad |b_j|=r
\quad(1\le j< n).
```


The phases of the b_j are arbitrary and may vary by edge. This includes every
Hermitian tridiagonal Toeplitz matrix. There is **no restriction relating r to
delta**, and r=0 is included.

### Theorem B (strengthening obtained during this audit)

For every n>=2, T in $`\mathcal T_n`$ with ||T||_2<=1, and 0<delta<1/2, an
O(n)-operation deterministic algorithm in the canonical model returns a real
D with ||D||_2<=delta and


```math
\mathop{\mathrm{gap}}\nolimits(T+D)\ge\frac{\delta}{n^3}
\ge\left(\frac{\delta}{n}\right)^3.                 \tag{3}
```


Thus the original output and complexity guarantees hold on this entire subclass
with the **universal** choices a=3, c_0=1, q=1 (and universal C).

**Algorithm.** Read the diagonals and, if desired, verify the class promise using
exact equality comparisons. Compute r^2=b_1\overline{b_1} from the two supplied
off-diagonals. If r^2<=delta^2/(16n^2), return


```math
D_{jj}=-\delta+\frac{2\delta(j-1)}{n-1}.              \tag{4}
```


Otherwise return D=0. No eigenvalues, eigenvectors, trigonometric values, phases,
or input bits are computed. Even square roots are unnecessary in this algorithm.

**Proof, weak branch.** If r<=delta/(4n), each off-diagonal row sum is at most
2r<=delta/(2n)<=delta/[2(n-1)]. The diagonal is constant, so its index order is
already a sorted order. Theorem A applies to (4), giving a gap at least delta/n,
which is at least delta/n^3.

**Proof, strong branch.** Here r>delta/(4n)>0. There is a diagonal unitary W
such that W*T W has diagonal tau and off-diagonals r. To see this directly, set
w_1=1 and w_{j+1}=\overline{b_j}w_j/r. Then |w_j|=1 and
$`\overline{w_j}b_j w_{j+1}=r`$. This is a proof of spectral equivalence;
the algorithm need not construct W.

Put h=pi/(n+1). For each k=1,...,n, the nonzero vector with entries sin(jkh)
(j=1,...,n) satisfies the tridiagonal eigenvalue equation, by
sin((j-1)kh)+sin((j+1)kh)=2cos(kh)sin(jkh), and vanishes at the fictitious
endpoints j=0,n+1. The n distinct eigenvalues are consequently


```math
\tau+2r\cos(kh),\qquad k=1,\ldots,n.
```


They are strictly decreasing. Every adjacent difference equals


```math
4r\sin((2k+1)h/2)\sin(h/2),\qquad 1\le k< n.
```


The first sine is at least sin(3h/2): its argument lies in the interval
[3h/2,pi-3h/2], and 0<3h/2<=pi/2 for n>=2. The elementary bound
sin(x)>=2x/pi for 0<=x<=pi/2 follows from concavity of sine and its chord on
that interval. Therefore


```math
\mathop{\mathrm{gap}}\nolimits(T)\ge\frac{12r}{(n+1)^2}
>\frac{3\delta}{n(n+1)^2}
\ge\frac{\delta}{n^3},                              \tag{5}
```


where the last inequality uses (n+1)^2<=3n^2 for every n>=2.
D=0 proves the required bound in this branch. The weak branch includes r=0
and equality at the branch threshold, so no case is omitted.

Both outputs have norm at most delta. Reading, testing the structural promise,
and writing n entries require O(n) arithmetic operations and comparisons.
Because 0<delta<1/2, delta>=delta^3, proving the second inequality in (3).
The input normalization ||T||_2<=1 was not needed in the proof, so in particular
it is respected rather than replaced. QED.

**Source relationship.** The workshop report arXiv:2602.05394v3, Problem 3.2,
suggests starting with tridiagonal Toeplitz matrices. Theorem B supplies one
explicit treatment of that suggested starting class and allows varying complex
phases. We do not claim that the classical sine-spectrum calculation is new,
or that this short combination has not appeared elsewhere.

## 5. Unrestricted order two

For any Hermitian 2x2 input with diagonal entries t_1,t_2, subtract delta from
the smaller diagonal entry and add delta to the larger (break a tie by index).
The new diagonal difference has magnitude |t_1-t_2|+2delta. Its eigenvalue gap is


```math
\sqrt{(|t_1-t_2|+2\delta)^2+4|b|^2}\ge2\delta.
```


The output has norm delta and costs O(1), without a coupling assumption.
This is an additional exact subcase, not an unrestricted all-n construction.

## 6. Status correspondence and exact gap remaining

Theorem A gives an all-dimensional weak-coupling class. Theorem B gives an
all-dimensional class with **arbitrarily strong or weak coupling** and every
allowed delta. Both preserve the field, norm, diagonal output, arithmetic model,
and nearly-linear complexity target. They prove cases *inside* the displayed
quantifiers, not a different computational task.

They do not cover general tridiagonal inputs with varying diagonal and varying
off-diagonal magnitudes outside Theorem A. No argument patches these cases into
an algorithm for all T. Thus no SOLUTION CLAIMED, SOLVED or LEAN VERIFIED
promotion is justified.

An OPEN -> PARTIAL proposal is reasonable under the repository's definition of
proved substantive subcases, subject to independent mathematical review and the
maintainer's judgment about substantive scope. The original target and its open
count must remain unchanged. This is a candidate update, not an accepted one.
