---
title: "MI-18: a counterexample to q-permanent monotonicity"
author: "Kenta Kitamura (formalization and supplied certificate); exposition prepared by Codex"
date: "6 October 2026"
document-kind: "Counterexample manuscript"
review-footer: "AI-prepared exposition of the supplied certificate; no human authorship, approval, or discovery priority is asserted."
---

The universal monotonicity assertion in MI-18 is false. An ordered family of 144 vectors in $\mathbb C^2$ gives a positive semidefinite Gram matrix whose $q$-permanent has a strictly negative derivative at $q=1$. Adding a sufficiently small positive multiple of the identity gives a positive definite counterexample as well. The proof reduces the sign of that derivative to a finite calculation with Gaussian integers; all input integers are printed in the appendix.

The certificate and Lean formalization were supplied by Kenta Kitamura in [issue #329](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/329). The source used here is fixed at [commit 4200da4fc1a132d69c23fb877795b5b72089544b](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/tree/4200da4fc1a132d69c23fb877795b5b72089544b). Codex prepared this conventional mathematical exposition and the accompanying independent Python checker. This is AI-prepared prose, not a manuscript written or approved by Kitamura. The source repository discloses AI assistance in its formalization and certificate development; no claim of external human review or discovery priority is made here.

## 1. Statement and construction

We index rows and columns by $0,\ldots,n-1$. This simply shifts the indices in MI-18 by one and preserves their order. For $\sigma\in S_n$, let

$$
\operatorname{inv}(\sigma)
=\#\{(i,j):0\le i<j<n,\ \sigma(i)>\sigma(j)\}.
$$

For a complex matrix $A=(A_{ij})$, put

$$
P_q(A)=\sum_{\sigma\in S_n}q^{\operatorname{inv}(\sigma)}
             \prod_{i=0}^{n-1}A_{i,\sigma(i)},\qquad 0^0=1.
\tag{1}
$$

In particular, $P_1(A)=\operatorname{per}(A)$. If $A$ is Hermitian, (1) is real for real $q$: conjugating a summand replaces $\sigma$ by $\sigma^{-1}$, and $\operatorname{inv}(\sigma^{-1})=\operatorname{inv}(\sigma)$. For the latter equality, an inversion $i<j$, $\sigma(i)>\sigma(j)$ corresponds to the inversion $(\sigma(j),\sigma(i))$ of $\sigma^{-1}$. Thus (1) defines an ordinary real polynomial in this case.

Let the ordered triples $(a_j,u_j,v_j)$ be those in the appendix, and set

$$
n=144,\qquad b_j=u_j+\mathrm{i}v_j,\qquad
V_{j,:}=(a_j,b_j),\qquad H=VV^*.
\tag{2}
$$

**Theorem.** The matrix $H$ is Hermitian positive semidefinite, has positive diagonal, is non-diagonal, and satisfies

$$
\left.\frac{d}{dq}P_q(H)\right|_{q=1}<0.
\tag{3}
$$

Moreover, there exist $\varepsilon>0$ and $0<q_1<q_2=1$ for which

$$
A=H+\varepsilon I_{144}>0,
\qquad P_{q_2}(A)<P_{q_1}(A).
\tag{4}
$$

Consequently both the positive semidefinite version stated in MI-18 and the positive definite version of the Bapat--Lal conjecture fail. The construction gives order 144; it makes no assertion that this is the smallest possible order. The proof of (4) is existential in $\varepsilon$ and $q_1$.

## 2. An endpoint derivative identity

For an arbitrary complex $n\times n$ matrix with $n\ge2$, write

$$
D(A)=\left.\frac{d}{dq}P_q(A)\right|_{q=1}
=\sum_{\sigma\in S_n}\operatorname{inv}(\sigma)
                         \prod_i A_{i,\sigma(i)}.
$$

If $I=\{i,j\}$ and $J=\{k,\ell\}$ with $i<j$ and $k<\ell$, write $A[I,J]$ for the corresponding $2\times2$ submatrix, with these increasing orders. The complementary submatrix is $A[I^c,J^c]$. The permanent of the empty matrix is understood to be 1. Define

$$
T(A)=\sum_{\substack{I,J\subseteq\{0,\ldots,n-1\}\\|I|=|J|=2}}
       \det A[I,J]\,\operatorname{per}A[I^c,J^c].
$$

**Lemma 1.** For every such matrix,

$$
2D(A)=\binom n2\operatorname{per}(A)-T(A).
\tag{5}
$$

**Proof.** Fix $i<j$ and put $M_\sigma=\prod_r A_{r,\sigma(r)}$. Separate the permanent into the sums $E_{ij}$ over permutations satisfying $\sigma(i)<\sigma(j)$ and $O_{ij}$ over those satisfying $\sigma(i)>\sigma(j)$. These two alternatives exhaust all permutations, so

$$
E_{ij}+O_{ij}=\operatorname{per}(A).
$$

For each permutation in $E_{ij}$, put $k=\sigma(i)<\ell=\sigma(j)$ and pair it with the permutation that exchanges the images of $i$ and $j$. Their difference is

$$
M_\sigma-M_{\sigma\circ(i\ j)}
=(A_{ik}A_{j\ell}-A_{i\ell}A_{jk})
                    \prod_{r\notin\{i,j\}}A_{r,\sigma(r)}.
$$

Fixing $k<\ell$ and summing over all bijections between the remaining row and column sets gives exactly

$$
E_{ij}-O_{ij}
=\sum_{k<\ell}\det A[\{i,j\},\{k,\ell\}]
             \operatorname{per}A[\{i,j\}^c,\{k,\ell\}^c].
$$

Now sum over $i<j$. A given $M_\sigma$ occurs in $\sum_{i<j}O_{ij}$ exactly $\operatorname{inv}(\sigma)$ times. Hence

$$
T(A)=\sum_{i<j}(E_{ij}-O_{ij})
=\binom n2\operatorname{per}(A)-2D(A),
$$

as required. No positivity assumption was used.

## 3. Permanents of two-coordinate Gram matrices

For polynomials of degree at most $m$, define the weighted coefficient pairing

$$
\langle f,h\rangle_m
=\sum_{k=0}^{m}k!(m-k)!\,[z^k]f\,\overline{[z^k]h},
\qquad \|f\|_m^2=\langle f,f\rangle_m.
\tag{6}
$$

Consider two families of $m$ vectors $(\alpha_i,\beta_i)$ and $(\gamma_j,\delta_j)$, and the matrix

$$
B_{ij}=\alpha_i\overline{\gamma_j}+\beta_i\overline{\delta_j}.
$$

Set $p_X(z)=\prod_i(\alpha_i+\beta_i z)$ and $p_Y(z)=\prod_j(\gamma_j+\delta_j z)$.

**Lemma 2.** One has

$$
\operatorname{per}(B)=\langle p_X,p_Y\rangle_m.
\tag{7}
$$

**Proof.** In the expansion of a permanent summand, let $R$ be the rows in which the second coordinate is chosen, and let $C$ be the columns matched to these rows. If $|R|=|C|=k$, exactly $k!(m-k)!$ permutations map $R$ bijectively onto $C$ and $R^c$ onto $C^c$. Their chosen-coordinate products are identical. Summing over $R$ gives

$$
\sum_{|R|=k}\prod_{i\in R}\beta_i\prod_{i\notin R}\alpha_i
=[z^k]p_X,
$$

and the column sum is the conjugate of $[z^k]p_Y$. Summing over $k$ proves (7), including $m=0$ by the empty-product convention.

Return to arbitrary ordered rows $(a_j,b_j)$ of a two-column matrix $V$, and put

$$
\ell_j(z)=a_j+b_jz,\qquad
p(z)=\prod_{j=0}^{n-1}\ell_j(z),\qquad H=VV^*.
$$

Taking the two families equal in (7) yields

$$
\operatorname{per}(H)=\|p\|_n^2.
\tag{8}
$$

For $I=\{i,j\}$, $i<j$, write

$$
w_I=a_i b_j-a_j b_i,\qquad
p_I(z)=\prod_{r\notin I}\ell_r(z),\qquad
F(z)=\sum_{|I|=2}w_I p_I(z).
$$

The $2\times2$ submatrix $H[I,J]$ equals $V[I,:]V[J,:]^*$, so

$$
\det H[I,J]=w_I\overline{w_J}.
$$

The complementary submatrix is likewise a mixed Gram matrix. Applying (7) with $m=n-2$ gives

$$
\operatorname{per}H[I^c,J^c]=\langle p_I,p_J\rangle_{n-2}.
$$

Substitution into $T(H)$ and expansion of the pairing now give

$$
\begin{aligned}
T(H)
&=\sum_{I,J}w_I\overline{w_J}\langle p_I,p_J\rangle_{n-2}\\
&=\sum_{k=0}^{n-2}k!(n-2-k)!
        \left|\sum_I w_I[z^k]p_I\right|^2
=\|F\|_{n-2}^2.
\end{aligned}
\tag{9}
$$

Together, (5), (8), and (9) prove the rank-two endpoint formula

$$
2D(H)=\binom n2\|p\|_n^2-\|F\|_{n-2}^2.
\tag{10}
$$

## 4. The wedge polynomial and its integer recurrence

To compute $F$ without summing over all pairs, define

$$
g(z)=\sum_{j=0}^{n-1}(n-1-2j)b_j
                         \prod_{r\ne j}\ell_r(z).
$$

**Lemma 3.** $F=-g$. In particular, $g$ has degree at most $n-2$.

**Proof.** The identity

$$
a_i b_j-a_j b_i=\ell_i(z)b_j-\ell_j(z)b_i
$$

implies

$$
w_{\{i,j\}}p_{\{i,j\}}(z)
=b_j\prod_{r\ne j}\ell_r(z)-b_i\prod_{r\ne i}\ell_r(z).
$$

In the sum over $i<j$, the term $b_j\prod_{r\ne j}\ell_r$ receives $j$ positive contributions from indices below $j$, and $n-1-j$ negative contributions from indices above it. Its net coefficient is therefore $2j-n+1$. This proves $F=-g$. Each summand defining $F$ has degree at most $n-2$, proving the degree assertion without dividing by any $\ell_j$ or coordinate.

For the certificate (2), put

$$
P=\|p\|_{144}^2,\qquad S=\|g\|_{142}^2.
$$

Then (10) becomes

$$
2D(H)=10296P-S,\qquad \binom{144}{2}=10296.
\tag{11}
$$

Here is a complete finite procedure for computing the two integers in (11). Use ascending coefficients and start with $p^{(0)}=1$ and $g^{(0)}=0$. For $j=0,\ldots,143$, successively form

$$
\begin{aligned}
p^{(j+1)}(z)&=(a_j+b_jz)p^{(j)}(z),\\
g^{(j+1)}(z)&=(a_j+b_jz)g^{(j)}(z)
                    +(143-2j)b_jp^{(j)}(z).
\end{aligned}
\tag{12}
$$

Induction shows that $p^{(j)}$ is the product of the first $j$ factors, and $g^{(j)}$ is the sum with one marked factor among those first $j$ factors, using the fixed final weights $143-2r$. Thus $p^{(144)}=p$ and $g^{(144)}=g$. More explicitly, if $c_{j,k}=[z^k]p^{(j)}$ and $d_{j,k}=[z^k]g^{(j)}$, take $c_{0,0}=1$, all other initial coefficients zero, and use

$$
\begin{aligned}
c_{j+1,k}&=a_jc_{j,k}+b_jc_{j,k-1},\\
d_{j+1,k}&=a_jd_{j,k}+b_jd_{j,k-1}
                          +(143-2j)b_jc_{j,k}.
\end{aligned}
$$

Coefficients outside their ranges are zero. Every operation is addition or multiplication of Gaussian integers. With $(x,y)$ representing $x+\mathrm{i}y$, these operations are

$$
(x,y)+(u,v)=(x+u,y+v),\qquad
(x,y)(u,v)=(xu-yv,xv+yu).
$$

After all 144 steps, the coefficient $d_{144,143}$ is exactly zero, as Lemma 3 also predicts. Take

$$
\begin{aligned}
P&=\sum_{k=0}^{144}k!(144-k)!
       \big((\operatorname{Re}c_{144,k})^2+(\operatorname{Im}c_{144,k})^2\big),\\
S&=\sum_{k=0}^{142}k!(142-k)!
       \big((\operatorname{Re}d_{144,k})^2+(\operatorname{Im}d_{144,k})^2\big).
\end{aligned}
$$

Evaluation on the appendix gives the exact integer inequalities

$$
P>0,\qquad 10300P<S<10301P.
\tag{13}
$$

The positivity of $P$ also follows directly: all the $a_j$ are nonzero, so $[z^0]p=\prod_j a_j\ne0$. The integers $P$ and $S$ have 768 and 772 decimal digits, respectively; their full decimal expansions are unnecessary for the sign test. For orientation only, division gives

$$
\frac SP\approx10300.4591950231122,\qquad
\frac{D(H)}P\approx-2.2295975115561.
$$

These decimal approximations are not used to establish (13). The exact lower bound alone gives

$$
2D(H)=10296P-S<-4P<0,
$$

which proves (3).

The machine-readable [certificate](certificate.json) contains only the ordered triples and provenance metadata. The separately written [Python checker](verify_certificate.py) uses arbitrary-precision integers from the Python standard library. It checks the coefficient cancellation, (13), the nonzero off-diagonal entry used below, and an additional recurrence for $F$. In this second recurrence, $p^{(j)}$ has the meaning above and $F^{(j)}$ is the wedge sum for the first $j$ rows. Adjoining row $j$ gives

$$
F^{(j+1)}
=\ell_jF^{(j)}+j b_jp^{(j)}-\ell_j\frac{d}{dz}p^{(j)},
\qquad F^{(0)}=0.
$$

Indeed the new pairs contribute $b_j\sum_{r<j}a_r\prod_{s<j,s\ne r}\ell_s-a_j(p^{(j)})'$, and the first sum equals $j p^{(j)}-z(p^{(j)})'$. This yields the displayed recurrence. The checker verifies that its final coefficient list is exactly the negative of that produced for $g$ by (12).

From the repository root, the complete numerical reproduction command is

```
python3 matrix-inequalities-and-norms/MI-18/verify_certificate.py
```

It returns `PASS` together with the exact rational bounds and hashes of the two computed integers. The finite arithmetic is independently reproducible from the appendix and (12); no copy of the external Lean project is needed for this calculation.

## 5. Positive definiteness and strict decrease

For every vector $x\in\mathbb C^{144}$,

$$
x^*Hx=x^*VV^*x=\|V^*x\|_2^2\ge0,
$$

so $H$ is Hermitian positive semidefinite. Its diagonal entries are $a_j^2+u_j^2+v_j^2>0$. The first two rows give

$$
\begin{aligned}
H_{0,1}
&=(-60)(-55)+(72-35\mathrm{i})(80+21\mathrm{i})\\
&=9795-1288\mathrm{i}\ne0,
\end{aligned}
$$

so $H$ is non-diagonal. This verifies every matrix hypothesis in the positive semidefinite formulation of MI-18.

Now put $A_\varepsilon=H+\varepsilon I_{144}$. For every $\varepsilon>0$ and $x\ne0$,

$$
x^*A_\varepsilon x=\|V^*x\|_2^2+\varepsilon\|x\|_2^2>0.
$$

The off-diagonal entry computed above is unaffected by this perturbation. Also $D(A_\varepsilon)$ is a polynomial in $\varepsilon$, by the finite sum defining $D$. It is therefore continuous at zero. Since $D(A_0)=D(H)<0$, there exists $\varepsilon_0>0$ such that

$$
D(A_\varepsilon)<0\qquad(0<\varepsilon<\varepsilon_0).
$$

Choose any such $\varepsilon$, and let $f(q)=P_q(A_\varepsilon)$. The function $f$ is a real polynomial with $f'(1)<0$. By the definition of the derivative, for all sufficiently small $h>0$,

$$
\frac{f(1)-f(1-h)}h<0.
$$

Taking $h<1$ gives $q_1=1-h\in(0,1)$, $q_2=1$, and $f(q_2)<f(q_1)$. This proves (4). The same argument applied directly to $H$ gives a strict decrease for the positive semidefinite witness.

The proof specifies neither a numerical perturbation size nor a numerical comparison point. In particular, it does not assert a decrease for a separately proposed fixed choice such as $10^{70}H+I$ at $q=1-10^{-70}$. It also gives no counterexample restricted to real symmetric matrices. These additional statements are unnecessary to disprove the universal complex Hermitian conjecture.

## Appendix. The ordered integer certificate

The table specifies $(a_j,u_j,v_j)$ with $b_j=u_j+\mathrm{i}v_j$. Each block lists a different range of row indices; use the displayed index $j$ to reconstruct the order $0,1,\ldots,143$. Simultaneously permuting rows and columns need not preserve the inversion-weighted polynomial, so this order is part of the mathematical data.

The triples are transcribed from Kitamura's [immutable certificate source](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/blob/4200da4fc1a132d69c23fb877795b5b72089544b/lean/Bapat/Certificate.lean). The accompanying JSON repeats precisely this small dataset, not the external proof repository. The source repository is distributed under [Apache-2.0](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/blob/4200da4fc1a132d69c23fb877795b5b72089544b/LICENSE); the data attribution and license provenance are recorded in the JSON.

| $j$ | $(a_j,u_j,v_j)$ | $j$ | $(a_j,u_j,v_j)$ | $j$ | $(a_j,u_j,v_j)$ |
|---:|:-----------------------|---:|:-----------------------|---:|:-----------------------|
| 0 | $(-60,72,-35)$ | 48 | $(61,58,54)$ | 96 | $(69,-10,-71)$ |
| 1 | $(-55,80,-21)$ | 49 | $(57,72,40)$ | 97 | $(95,30,-1)$ |
| 2 | $(52,-85,-1)$ | 50 | $(42,88,-22)$ | 98 | $(78,7,-62)$ |
| 3 | $(49,-84,21)$ | 51 | $(-53,-83,-15)$ | 99 | $(84,17,-51)$ |
| 4 | $(63,-61,48)$ | 52 | $(38,59,-71)$ | 100 | $(90,26,-36)$ |
| 5 | $(52,-68,52)$ | 53 | $(42,76,-50)$ | 101 | $(95,27,-18)$ |
| 6 | $(68,-51,53)$ | 54 | $(40,-7,-91)$ | 102 | $(92,-7,38)$ |
| 7 | $(39,-83,40)$ | 55 | $(41,34,-84)$ | 103 | $(98,19,6)$ |
| 8 | $(-41,91,5)$ | 56 | $(79,5,61)$ | 104 | $(66,-37,-65)$ |
| 9 | $(45,-58,68)$ | 57 | $(77,29,57)$ | 105 | $(94,16,-29)$ |
| 10 | $(59,-46,66)$ | 58 | $(74,46,49)$ | 106 | $(98,17,-12)$ |
| 11 | $(30,-95,7)$ | 59 | $(68,65,33)$ | 107 | $(90,8,-42)$ |
| 12 | $(32,-60,73)$ | 60 | $(-55,-79,27)$ | 108 | $(99,7,14)$ |
| 13 | $(48,-83,-27)$ | 61 | $(65,75,12)$ | 109 | $(97,-1,25)$ |
| 14 | $(49,-32,81)$ | 62 | $(61,79,-11)$ | 110 | $(-77,20,61)$ |
| 15 | $(-21,79,-57)$ | 63 | $(52,-56,-64)$ | 111 | $(100,6,-1)$ |
| 16 | $(-44,80,41)$ | 64 | $(50,-29,-82)$ | 112 | $(-85,6,52)$ |
| 17 | $(63,-29,72)$ | 65 | $(-55,-65,53)$ | 113 | $(87,-27,41)$ |
| 18 | $(36,-19,91)$ | 66 | $(77,54,33)$ | 114 | $(66,-54,-53)$ |
| 19 | $(21,-23,95)$ | 67 | $(-51,-4,86)$ | 115 | $(92,-19,33)$ |
| 20 | $(14,-99,-4)$ | 68 | $(75,65,15)$ | 116 | $(99,1,-15)$ |
| 21 | $(-33,80,51)$ | 69 | $(-54,-38,75)$ | 117 | $(96,-2,-28)$ |
| 22 | $(-73,36,-59)$ | 70 | $(84,-11,54)$ | 118 | $(92,-9,-39)$ |
| 23 | $(-48,1,-88)$ | 71 | $(71,69,-10)$ | 119 | $(84,-22,-49)$ |
| 24 | $(-19,75,64)$ | 72 | $(61,49,-62)$ | 120 | $(-98,12,-14)$ |
| 25 | $(31,21,93)$ | 73 | $(66,63,-41)$ | 121 | $(76,-39,-52)$ |
| 26 | $(59,-6,80)$ | 74 | $(84,37,40)$ | 122 | $(99,-12,3)$ |
| 27 | $(2,93,-37)$ | 75 | $(86,18,48)$ | 123 | $(99,-13,-9)$ |
| 28 | $(5,84,-55)$ | 76 | $(-72,-62,31)$ | 124 | $(96,-17,-24)$ |
| 29 | $(16,70,70)$ | 77 | $(60,14,-79)$ | 125 | $(95,-23,20)$ |
| 30 | $(45,28,85)$ | 78 | $(81,59,-3)$ | 126 | $(91,-27,-33)$ |
| 31 | $(-24,-75,-61)$ | 79 | $(84,53,13)$ | 127 | $(85,-36,-39)$ |
| 32 | $(27,-43,-86)$ | 80 | $(79,57,-20)$ | 128 | $(95,-27,-16)$ |
| 33 | $(34,65,68)$ | 81 | $(88,41,25)$ | 129 | $(69,-61,-39)$ |
| 34 | $(70,-7,72)$ | 82 | $(90,26,36)$ | 130 | $(96,-28,-2)$ |
| 35 | $(-61,-18,-77)$ | 83 | $(73,45,-51)$ | 131 | $(86,-40,32)$ |
| 36 | $(45,60,67)$ | 84 | $(69,30,-66)$ | 132 | $(78,-51,-36)$ |
| 37 | $(54,42,73)$ | 85 | $(89,4,46)$ | 133 | $(94,-34,8)$ |
| 38 | $(20,47,-86)$ | 86 | $(91,39,13)$ | 134 | $(90,-39,22)$ |
| 39 | $(28,96,6)$ | 87 | $(89,45,-2)$ | 135 | $(89,-42,-17)$ |
| 40 | $(76,-20,62)$ | 88 | $(61,-22,-76)$ | 136 | $(83,-52,-22)$ |
| 41 | $(25,86,-44)$ | 89 | $(82,42,-39)$ | 137 | $(88,-47,-7)$ |
| 42 | $(28,10,-96)$ | 90 | $(86,43,-27)$ | 138 | $(-73,64,24)$ |
| 43 | $(41,-51,-76)$ | 91 | $(90,41,-15)$ | 139 | $(87,-49,7)$ |
| 44 | $(44,82,37)$ | 92 | $(71,9,-70)$ | 140 | $(84,-50,22)$ |
| 45 | $(71,16,68)$ | 93 | $(80,29,-53)$ | 141 | $(76,-63,-12)$ |
| 46 | $(66,39,64)$ | 94 | $(95,24,20)$ | 142 | $(82,-57,10)$ |
| 47 | $(42,91,6)$ | 95 | $(94,12,31)$ | 143 | $(79,-62,-1)$ |

## Sources and scope

- R. B. Bapat and A. K. Lal, *Inequalities for the q-permanent*, Linear Algebra and its Applications 197-198 (1994), 397-409, [original paper](https://doi.org/10.1016/0024-3795(94)90497-9).
- L. Mitchell, *A note on Bapat's q-permanent conjecture*, Operators and Matrices 14 (2020), 915-919, [primary paper](https://files.ele-math.com/articles/oam-14-56.pdf), for the positive semidefinite formulation and earlier special cases.
- Kenta Kitamura, [submission in issue #329](https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/329), supplying the certificate and formalization used here.
- Kenta Kitamura, [complete proof entry point](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/blob/4200da4fc1a132d69c23fb877795b5b72089544b/lean/Bapat/Main.lean) and [source README](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/blob/4200da4fc1a132d69c23fb877795b5b72089544b/README.md), at the fixed commit cited above. The formal target there is the positive definite complex Hermitian conjecture on $[-1,1]$.
- [MI-18's canonical statement](README.md). Its broader positive semidefinite formulation is contradicted directly by $H$, as shown in Sections 4 and 5.

The mathematical derivation above and the integer checker establish the counterexample without treating a reported Lean build as a premise. The repository's separate verification record distinguishes the source and build evidence for the external formalization from this independently reproduced arithmetic and exposition.
