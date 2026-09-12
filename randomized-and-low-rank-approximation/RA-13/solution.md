---
title: "RA-13: the absolute-error threshold for extremal Gaussian trace bounds"
author: "George Stepaniants"
affiliation: "Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA"
date: "11 September 2026"
document-kind: "Verified resolution"
review-footer: "Independent Codex-agent review; not external human peer review or formal certification."
lang: "en-GB"
---

**Verification status: independent-agent PASS.** This manuscript proves the complete canonical RA-13 probability chain, including indefinite matrices and the stated threshold endpoint. It was developed with substantial ChatGPT/Codex assistance. A separate agent independently checked the full argument, exact target, published bell-shape theorem, grouped transfers and all limiting steps. [Detailed independent review](../../references/stepaniants-ra13-2026-09-11/verification/RA-13-independent-review.md).

The mathematical body in Sections 1-8 is unchanged from the reviewed proof apart from two explicitly permitted LaTeX spacing corrections and restoration of the Greek letter in one function definition. [The submission record](../../references/stepaniants-ra13-2026-09-11/README.md) retains the original source, exact hashes and verification evidence. Kwaśnicki's published bell-shape theorem and Hallman's centered coefficient-derivative method retain their attribution. Verification is independent automated-agent review, not external human peer review or formal proof certification.

## 1. Normalized theorem

Let $\alpha>0$, let $G_i$ be independent $\operatorname{Gamma}(\alpha,1)$ variables (shape and rate), and let $w$ be a finite nonzero real vector with $|w_i|\le1$. Write

$$
Z_w=\sum_iw_i(G_i-\alpha),\qquad
r=\sum_iw_i^2,\qquad v=\alpha r>0,
\qquad H(v)=1+\sqrt{v+1}.
$$

Let $w^*$ consist of $\lfloor r\rfloor$ ones, the additional coefficient $\sqrt{r-\lfloor r\rfloor}$, and any zero padding. Let $J\sim\operatorname{Gamma}(v,1)$. The proposed stronger assertion is

$$
\Pr(Z_w\ge h)\le\Pr(Z_{w^*}\ge h)
\le\Pr(J-v\ge h),\qquad h\ge H(v).                 \tag{1}
$$

The same first inequality applied to $-w$, followed by addition of the two tails, gives

$$
\Pr(|Z_w|\ge h)\le2\Pr(Z_{w^*}\ge h)
\le2\Pr(J-v\ge h).                                \tag{2}
$$

## 2. External shape theorem and the regularity used

Kwaśnicki, *A new class of bell-shaped functions*, arXiv:1710.11023v3, Corollary 1.2, proves weak bell-shape for extended generalized Gamma convolutions. Its hypotheses apply to a finite sum of signed Gamma variables, with an arbitrary deterministic shift and an independent Gaussian: on each half-line, the Levy density multiplied by the absolute jump size is a finite nonnegative sum of exponentials. Gaussian convolution makes the density smooth and strictly bell-shaped. In particular its second derivative has exactly two sign changes, with signs $+,-,+$. Section 2 also explains preservation of the upper bound on sign changes under pointwise limits of derivatives. [Primary theorem and explanation](https://arxiv.org/html/1710.11023v3).

For a sum of positive Gamma variables with total shape $R>2$, the density extended by zero is $C^1$, and is analytic strictly inside its support; its density and first derivative vanish at the finite support endpoint and at infinity. These facts follow directly by scaling the convolution simplex: its density is a positive constant times $x^{R-1}$ times a positive analytic function at zero, after translation. Gaussian smoothing and the cited theorem show that its second derivative has at most two sign changes inside the support. The derivative is positive near the left endpoint and negative somewhere later; the second derivative is positive near the endpoint, negative somewhere and positive eventually. Thus the second-derivative pattern is $+,-,+$. Consequently the positive global maximum of $g=-f'$ is attained at the upper transition, and $f''\ge0$ to its right. Isolated zeros without a sign change do not affect this assertion.

For signed sums we use a strictly positive Gaussian variance until the final limit, thereby avoiding any differentiability issue at the point where positive and negative Gamma supports meet.

## 3. An inflection identity

Consider

$$
Y=c+\sum_i w_i H_i+\tau N,
$$

where $H_i\sim\operatorname{Gamma}(r_i,1)$ are independent, $r_i>0$, all $w_i\ne0$, $N\sim N(0,1)$ is independent, and $c$ is deterministic. Put

$$
M=\mathbb EY,\quad V=\sum_i r_iw_i^2,\quad R=\sum_i r_i.
$$

Initially suppose $\tau>0$. Let $f$ be the smooth density, and let $z$ be a global maximum of $g=-f'$. Then $g(z)>0$, $g'(z)=0$, and $g''(z)\le0$. Put

$$
d=z-M,\qquad h_0=f(z)/g(z),\qquad
\nu(t)=1-g(z-t)/g(z)\ge0.
$$

Define the nonnegative component kernels and their signed first and positive second moments by

$$
K_{0,i}(t)=\frac{r_i}{|w_i|}e^{-|t|/|w_i|}\mathbf1_{tw_i>0},
\qquad K_0=\sum_iK_{0,i},
\quad K_1=\sum_iw_iK_{0,i},
\quad K_2=\sum_iw_i^2K_{0,i}.
$$

Their integrals are $R$, $M_0=\sum_i r_iw_i$, and $V$, respectively. In distributional differentiation,

$$
K_2'=-K_1+M_0\delta_0,
\qquad K_2''=K_0-R\delta_0+M_0\delta_0'.             \tag{3}
$$

The centered Gamma Stein identity, or differentiation of the characteristic function, gives

$$
(x-M)f(x)=-\tau^2f'(x)-(K_2*f')(x)
=\tau^2g(x)+(K_2*g)(x).                            \tag{4}
$$

Set

$$
A_0=\int K_1(t)\nu(t)\,dt,
\qquad B_0=\int K_2(t)\nu(t)\,dt,
\qquad C_0=\int K_0(t)\nu(t)\,dt.
$$

All are finite because $g$ is bounded and the kernels are integrable. Evaluating (4) at $z$, and differentiating it once using (3), gives respectively

$$
dh_0=\tau^2+V-B_0,
\qquad h_0-d=A_0.
$$

Differentiating (4) a second time at $z$, and again using (3), gives

$$
-2g(z)=\tau^2g''(z)+(K_0*g)(z)-Rg(z),
\qquad C_0=2+\tau^2g''(z)/g(z)\le2.                \tag{5}
$$

There is therefore a nonnegative measure $\mu$ on the finite set $\{0,w_1,\ldots,w_n\}$: give $w_i$ mass $\int K_{0,i}\nu$, combining masses at coincident scales, and place mass $2-C_0$ at scale zero. It satisfies

$$
\mu(\mathbb R)=2,
\quad\int w\,d\mu(w)=A_0,
\quad\int w^2\,d\mu(w)=B_0,
$$

and elimination of $h_0$ yields the exact identity

$$
d^2+\int (dw+w^2)\,d\mu(w)=V+\tau^2.             \tag{6}
$$

If $b\le0$ is a lower bound for all component scales, it is also a lower bound for the added zero. Whenever $d\ge-2b$, the function $w\mapsto dw+w^2$ is increasing on $[b,\infty)$, so (6) implies

$$
d^2+2db+2b^2\le V+\tau^2,
\qquad (d+b)^2\le V+\tau^2-b^2.                   \tag{7}
$$

The same identities hold with $\tau=0$ for positive Gamma sums of total shape $R>2$, evaluated at the positive maximum of $g=-f'$ described in Section 2. This point is strictly inside the support, where all derivatives are smooth. Equation (5) then gives $C_0=2$ exactly, and there is no atom at zero. Hence the measure is supported on the actual positive scales and (7) holds for their positive minimum $b$ as soon as $d\ge0$. The convolution differentiations are valid because $f,f'$ vanish at the finite support endpoint, $f''$ is locally integrable there, and all quantities decay exponentially at infinity.

## 4. The required convexity along selected transfers

Let $Z_w$ be centered as in Section 1, with variance $v$. Choose two nonzero coefficients $a,b$ and augment by independent rate-one exponentials:

$$
Y=Z_w+aE_1+bE_2+\tau N.
$$

The Gamma component mean after centering is $M=a+b$, and its variance before the Gaussian is

$$
V=v+a^2+b^2.
$$

There are two cases used below.

**Signed case.** Assume $0<a\le1$ and $-1\le b<0$ is a minimum coefficient of the entire vector $w$. Take $\tau>0$. Suppose the upper inflection point $z$ exceeded $H(v+\tau^2)$. Since $H(v+\tau^2)>2$,

$$
d=z-a-b>2-a-b\ge-2b,
$$

where the last inequality follows from $a\le1$ and $b\ge-1$. Equation (7) gives

$$
(z-a)^2\le v+\tau^2+a^2.
$$

Here $z-a>0$, and thus

$$
z\le a+\sqrt{v+\tau^2+a^2}
\le1+\sqrt{v+\tau^2+1}=H(v+\tau^2),
$$

a contradiction. By strict bell-shape, the augmented density is convex for all $x\ge H(v+\tau^2)$.

**Positive case.** Assume all nonzero coefficients are positive, and $0<b\le a\le1$ with $b$ a minimum positive coefficient. Take $\tau=0$. The augmented total shape exceeds two. If its upper inflection point satisfied $z>H(v)>2$, then $d=z-a-b>0$, so the positive version of (7) again yields

$$
z\le a+\sqrt{v+a^2}\le H(v).
$$

Therefore the augmented density is convex for $x\ge H(v)$.

## 5. Removing negative coefficients by grouped transfers

Fix $\tau>0$ and temporarily add $\tau N$ to every centered law. Choose all coefficients equal to the globally smallest negative value $b<0$; suppose their number is $l$. Choose a nonnegative coefficient $0\le a<1$, padding a zero coordinate if necessary. Vary this group by

$$
a(t)=\sqrt{a^2+lt},\qquad
b(t)=-\sqrt{b^2-t}
$$

with each of the $l$ minimum coefficients replaced by $b(t)$. Stop at the first of: $a(t)=1$; $b(t)$ reaches the next larger negative value; or $b(t)=0$. At a negative-level meeting, join every coefficient at that level to the minimum group before continuing. Throughout the open transfer interval, $a(t)>0$, $b(t)<0$ is a global minimum, and the coefficient bounds and sum of squares are preserved.

Hallman's centered coefficient-derivative calculation (Appendix A.2) gives, for a single square transfer $a^2\mapsto a^2+t$, $b^2\mapsto b^2-t$,

$$
\frac{d}{dt}\Pr(Z_{w(t)}+\tau N\le x)
=\frac\alpha2(b(t)-a(t))\,g_t''(x),                \tag{8}
$$

where $g_t$ is the density augmented by $a(t)E_1+b(t)E_2$, and includes the Gaussian. For the grouped transfer, the derivative is the sum of $l$ such terms. All their augmented distributions are identical, since the selected negative coefficients coincide. Thus its derivative is $l$ times the right-hand side of (8).

One may also verify (8) directly: the Laplace transform of the centered law is

$$
L(s)=\prod_i e^{\alpha w_i s}(1+w_i s)^{-\alpha}
$$

in a strip about zero. Differentiation with respect to the pair's transferred square gives

$$
\partial_t\bigl(L(s)/s\bigr)
=\frac\alpha2(b-a)s^2\frac{L(s)}{(1+as)(1+bs)},
$$

which is the transform of the right-hand side in (8). A Gaussian factor is independent of the coefficients and remains unchanged. Gaussian smoothing makes density/CDF differentiation and transform inversion valid on compact open transfer intervals; limits handle a starting zero coefficient or a vanishing endpoint coefficient.

Section 4 gives $g_t''(x)\ge0$ when $x\ge H(v+\tau^2)$, while $b(t)-a(t)<0$. The upper tail is therefore nondecreasing along every grouped transfer.

This procedure terminates after finitely many stages. A minimum group can merge with another negative level only finitely many times. Each time a nonnegative coefficient reaches one, it is permanently set aside; their number is at most $\lfloor r\rfloor$. If neither event occurs, all coefficients in the minimum group reach zero. New zero coordinates are introduced only when a new receiver is needed. Thus all negative coefficients are eventually eliminated, producing a nonnegative vector $u$ with the same sum of squares and the same cap.

For every $x\ge H(v+\tau^2)$,

$$
\Pr(Z_w+\tau N\ge x)\le\Pr(Z_u+\tau N\ge x).
$$

The path depends only on the coefficients, not on $\tau$. Let $\tau\downarrow0$, taking $x=h+H(v+\tau^2)-H(v)$ for any fixed $h\ge H(v)$. Nonzero finite signed Gamma sums have continuous distributions, so weak convergence gives

$$
\Pr(Z_w\ge h)\le\Pr(Z_u\ge h).                    \tag{9}
$$

## 6. Concentrating nonnegative coefficients

If the nonnegative vector $u$ has more than one coefficient strictly between zero and one, choose a smallest positive fractional coefficient $b$ and any other fractional coefficient $a\ge b$. Because all nonfractional positive coefficients equal one, $b$ is a minimum positive coefficient of the full vector. Make the square transfer

$$
a(t)=\sqrt{a^2+t},\qquad b(t)=\sqrt{b^2-t},
\quad 0\le t\le\min(1-a^2,b^2).
$$

The coefficient $b(t)$ remains a minimum positive coefficient on the open interval. The positive case of Section 4 and (8), now without a Gaussian, show that the upper tail at $h\ge H(v)$ is nondecreasing. The derivative identity is justified either by Hallman's Appendix A.2 or the same transform calculation; the two positive augmentations give total shape greater than two and zero boundary values of the relevant derivatives. Each stage makes at least one fractional coefficient zero or one, so finitely many stages produce $w^*$, up to permutation and zero padding. Together with (9), this proves the first inequality in (1).

## 7. Infinite divisibility and the Gamma endpoint

For each integer $N\ge1$, split each $G_i$ into $N$ independent Gamma variables of shape $\alpha/N$ and rate one. The centered weighted law is unchanged, the coefficient vector repeats each $w_i$ exactly $N$ times, and the total variance remains $v$. Apply the already proved first inequality of (1) with common shape $\alpha/N$ and sum of squared coefficients $Nr$.

Its extremal centered law is

$$
J_N-c_N+s_N(K_N-\alpha/N),
\quad c_N=\frac\alpha N\lfloor Nr\rfloor,
\quad s_N=\sqrt{Nr-\lfloor Nr\rfloor},
$$

where $J_N\sim\operatorname{Gamma}(c_N,1)$ and $K_N\sim\operatorname{Gamma}(\alpha/N,1)$ are independent; the zero-shape term is omitted if $c_N=0$. For all sufficiently large $N$, $c_N>0$, and $c_N\to v$. The residual has mean zero and variance $s_N^2\alpha/N\le\alpha/N$, so it tends to zero in probability. Thus the law converges to $J-v$ with $J\sim\operatorname{Gamma}(v,1)$. Its CDF is continuous. Passing to the limit proves the Gamma upper bound for every input vector, and in particular for $w^*$, completing (1) and (2).

## 8. Conversion to the exact RA-13 statement

For the canonical real symmetric $A\ne0$, let $\lambda=\|A\|_2$, $\phi=\|A\|_F$, and let $\lambda_i(A)$ be its signed eigenvalues. Set

$$
\alpha=m/2,\qquad w_i=\lambda_i(A)/\lambda,
\qquad r=\rho=\phi^2/\lambda^2,\qquad v=m\rho/2.
$$

Rotational invariance and $\chi_m^2/2\sim\operatorname{Gamma}(m/2,1)$ give

$$
T_m(A)-\operatorname{tr}A\ \stackrel d=\ \frac{2\lambda}{m}Z_w.
$$

The vector $w^*$ is exactly the normalized spectrum defining the canonical $B_{\lambda,\phi}$. Also $(2\lambda/m)J$ has the canonical Gamma law with shape $m\rho/2$ and rate $m/(2\lambda)$, and its mean is $\phi^2/\lambda$.

Finally, the canonical hypothesis on $\varepsilon$ is exactly

$$
h=\frac{m\varepsilon}{2\lambda}
\ge1+\sqrt{m\rho/2+1}=H(v).
$$

Equation (2) therefore gives both displayed canonical probability comparisons, including the endpoint and arbitrary indefinite matrices. No assertion about Hallman's disproved general auxiliary inflection conjecture is needed: convexity is only used along the selected grouped/minimum-coefficient paths.

## References and source check

1. Eric Hallman, *Extremal bounds for Gaussian trace estimation*, arXiv:2411.15454v1 (2024), Theorem 7 and Conjecture 4; Appendix A.2 for the centered square-transfer derivative. [Pinned primary text](https://arxiv.org/html/2411.15454v1). Its [current record](https://arxiv.org/abs/2411.15454), checked 11 September 2026, lists only v1, submitted 23 November 2024.
2. Mateusz Kwaśnicki, *A new class of bell-shaped functions*, arXiv:1710.11023v3, Corollary 1.2 and Section 2. [Pinned primary text](https://arxiv.org/html/1710.11023v3).
3. *Absolute-error threshold for extremal Gaussian trace bounds*, retained canonical RA-13 statement in OpenProblemsInNLA. [Canonical entry](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/randomized-and-low-rank-approximation/RA-13/README.md).

The earlier auxiliary mode/inflection counterexamples by Matthew J. Colbrook remain valid and separately attributed on the canonical page. They refute broader auxiliary assertions; this proof uses selected coefficient paths and establishes the final probability comparisons. [Submission and public-status audit](../../references/stepaniants-ra13-2026-09-11/README.md).
