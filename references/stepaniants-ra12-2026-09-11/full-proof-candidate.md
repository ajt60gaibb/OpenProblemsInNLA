# RA-12: the relative-error threshold for extremal Gaussian trace bounds

**George Stepaniants**  
Department of Computing and Mathematical Sciences  
California Institute of Technology  
11 September 2026

**Research proof candidate.** Prepared with substantial ChatGPT/Codex assistance. The exact submitted version and independent verification status must be recorded separately. The proof below treats the complete canonical probability chain, not the stronger auxiliary mode-location conjecture.

## The statement

For a real symmetric matrix $D$ and a positive integer $m$, let

$$
T_m(D)=\frac1m\sum_{j=1}^m z_j^TDz_j,
\qquad z_j\overset{\mathrm{iid}}\sim N(0,I).
$$

Let $A\ne0$ be positive semidefinite, and define

$$
\mu=\frac{\operatorname{tr}A}{\|A\|_2}\ge1,
\qquad
B_\mu=\frac1\mu\operatorname{diag}
\bigl(I_{\lfloor\mu\rfloor},\mu-\lfloor\mu\rfloor\bigr).
$$

A zero last entry is allowed. Gamma distributions below use shape and rate parameters.

**Theorem 1 (the full RA-12 comparison).** If $X\sim\operatorname{Gamma}(m\mu/2,m\mu/2)$, then for every $\varepsilon\ge2/(m\mu)$,

$$
\Pr\bigl(|T_m(A)-\operatorname{tr}A|\ge\varepsilon\operatorname{tr}A\bigr)
\le\Pr\bigl(|T_m(B_\mu)-1|\ge\varepsilon\bigr)
\le\Pr\bigl(|X-1|\ge\varepsilon\bigr).
$$

The proof establishes each upper-tail and lower-tail comparison separately at these thresholds. The matrices may have any finite dimensions; their random vectors need not be coupled.

## A mode bound for Gamma convolutions

We use the classical unimodality of finite sums of independent positive Gamma random variables. An explicit primary statement covering different shapes and scales is [Roosta-Khorasani and Székely, Theorem 4](https://arxiv.org/html/1601.04731v1), Appendix A. The same source's Lemma 5 records positivity, analyticity on the positive half-line and the behavior at zero. We use unimodality, not the auxiliary mode bound conjectured in Hallman.

The following location bound follows directly from the density's convolution equation.

**Lemma 2 (mode lies between mean minus extreme scales).** Let $Y$ be a finite sum of independent Gamma variables with positive shapes $r_i$ and positive scales $w_i$, and assume $\sum_i r_i>1$. Let

$$
M=\mathbb EY=\sum_i r_iw_i,
\qquad w_- =\min_iw_i,\quad w_+=\max_iw_i.
$$

Its positive mode $z$ satisfies

$$
M-w_+\le z\le M-w_-.
$$

**Proof.** Let $f$ be the density, extended by zero to negative arguments, and put

$$
k(t)=\sum_i r_i e^{-t/w_i},\qquad t\ge0.
$$

The Laplace transform is $L(u)=\prod_i(1+w_i u)^{-r_i}$ for $u>0$. Hence

$$
-L'(u)=L(u)\sum_i\frac{r_iw_i}{1+w_i u}.
$$

Uniqueness of Laplace transforms gives the density identity

$$
xf(x)=\int_0^x k(t)f(x-t)\,dt\qquad(x>0).
$$

The density is positive and smooth for $x>0$, vanishes at zero because $\sum_i r_i>1$, and tends to zero at infinity. Therefore its global mode is attained at a positive point $z$, with $f(z)>0$ and $f'(z)=0$. Differentiating the convolution by differentiating its smooth kernel gives

$$
f(x)+xf'(x)=k(0)f(x)+\int_0^x k'(t)f(x-t)\,dt.
$$

Define, for $t\ge0$,

$$
v(t)=1-\frac{f(z-t)}{f(z)}.
$$

Since $z$ is a global mode, $0\le v(t)\le1$. The first convolution identity at $z$, together with $\int_0^\infty k(t)\,dt=M$, yields

$$
M-z=\int_0^\infty k(t)v(t)\,dt.
$$

The differentiated identity at $z$, together with $\int_0^\infty[-k'(t)]\,dt=k(0)$, yields

$$
1=\int_0^\infty[-k'(t)]v(t)\,dt.
$$

Term by term in the definition of $k$,

$$
w_-[-k'(t)]\le k(t)\le w_+[-k'(t)].
$$

Integrating these inequalities against $v(t)\ge0$ proves
$w_-\le M-z\le w_+$, as required. All integrals are finite because $v\le1$ and $k,-k'$ are integrable. $\square$

## Transfers that respect the coefficient cap

Fix any $\alpha>0$, and let $G_i\overset{\mathrm{iid}}\sim\operatorname{Gamma}(\alpha,1)$. For a finite vector $w$ with $0\le w_i\le1$, put

$$
Q_w=\sum_i w_iG_i,
\qquad \sigma=\sum_iw_i>0,
\qquad \rho=\alpha\sigma.
$$

Let $w^{\mathrm{ext}}$ consist of $\lfloor\sigma\rfloor$ ones, the remaining entry $\sigma-\lfloor\sigma\rfloor$, and zeros as necessary. Its coordinates sum to $\sigma$. The zero entries have no effect on the distribution.

**Lemma 3 (extremal capped coefficients).** For every such $w$,

$$
\Pr(Q_w\ge x)\le\Pr(Q_{w^{\mathrm{ext}}}\ge x)
\qquad(x\ge\rho+1),
$$

and

$$
\Pr(Q_w\le x)\le\Pr(Q_{w^{\mathrm{ext}}}\le x)
\qquad(x\le\rho-1).
$$

In particular, for every $h\ge1$,

$$
\Pr(|Q_w-\rho|\ge h)
\le\Pr(|Q_{w^{\mathrm{ext}}}-\rho|\ge h).
$$

**Proof.** If at most one coordinate lies strictly between zero and one, the vector is already $w^{\mathrm{ext}}$ up to permutation. Otherwise choose a smallest strictly fractional coordinate $b$ and any other fractional coordinate $a\ge b$. All positive coordinates of $w$ are at least $b$, since the remaining nonfractional positive coordinates equal one.

Replace this pair by

$$
a(t)=a+t,\qquad b(t)=b-t,
\qquad 0\le t\le t_*:=\min\{1-a,b\}.
$$

The sum of the weights, and therefore the mean $\rho$, stays fixed. At the endpoint, at least one fractional coordinate becomes zero or one. For $0\le t<t_*$, $b(t)>0$ remains a minimum positive coefficient of the complete vector, every coefficient is at most one, and $a(t)\ge b(t)$.

Write $Q_t$ for the corresponding weighted Gamma sum, and let $E_1,E_2$ be independent rate-one exponentials, independent of the Gamma sum. Denote the density of

$$
Y_t=Q_t+a(t)E_1+b(t)E_2
$$

by $g_t$. All positive scales of $Y_t$ lie in $[b(t),1]$; its mean is $\rho+a(t)+b(t)$; and its total shape is greater than two. Lemma 2 therefore bounds its mode $z_t$ by

$$
\rho-1
\le \rho+a(t)+b(t)-1
\le z_t
\le \rho+a(t)+b(t)-b(t)
=\rho+a(t)\le\rho+1.
$$

By the cited unimodality theorem, $g_t'(x)\ge0$ for $0<x\le\rho-1$, when this interval is nonempty, and $g_t'(x)\le0$ for $x\ge\rho+1$.

For completeness, the precise coefficient derivative is

$$
\frac{\partial}{\partial t}\Pr(Q_t\le x)
=\alpha\bigl(a(t)-b(t)\bigr)g_t'(x),\qquad x>0.
$$

This is the identity used in [Hallman, Appendix A.1](https://arxiv.org/html/2411.15454v1#A1). It also follows directly here. The Laplace transform of the CDF of $Q_t$ is $L_{Q_t}(u)/u$, and differentiation gives

$$
\frac{\partial}{\partial t}\frac{L_{Q_t}(u)}u
=\alpha\bigl(a(t)-b(t)\bigr)u
\frac{L_{Q_t}(u)}{(1+a(t)u)(1+b(t)u)}
=\alpha\bigl(a(t)-b(t)\bigr)uL_{Y_t}(u).
$$

The inverse transform is the displayed formula because $g_t(0)=0$. Differentiation under the transform and inversion are justified on every compact subinterval of $[0,t_*)$: all varying scales are bounded away from zero there, and the finite Gamma convolution densities and their parameter derivatives have exponential decay and the standard locally integrable behavior at zero. Equivalently, the cited coefficient-derivative identity applies directly to the two changing positive coefficients.

The prefactor is nonnegative. Thus the lower CDF is nondecreasing along the transfer for $x\le\rho-1$, while the upper CDF is nonincreasing for $x\ge\rho+1$. The claims for $x\le0$ are immediate, since a nonzero weighted Gamma sum is strictly positive almost surely. Continuity of the distributions in the coefficients gives the same inequalities at $t=t_*$, including an endpoint with $b(t_*)=0$.

Each transfer strictly reduces the number of fractional coordinates. After finitely many transfers there is at most one, and the resulting vector is exactly $w^{\mathrm{ext}}$ up to zeros and permutation. Iterating the tail comparisons proves the two displayed one-sided bounds. Each nonzero weighted Gamma sum has a continuous distribution, so strict versus non-strict inequalities at the finite tail endpoints make no difference. Adding the lower and upper tails at $\rho-h$ and $\rho+h$ proves the last assertion. $\square$

## Passage to the Gamma upper bound

**Lemma 4 (Gamma comparison).** With the notation of Lemma 3, let $H\sim\operatorname{Gamma}(\rho,1)$. Then

$$
\Pr(Q_w\ge x)\le\Pr(H\ge x)\quad(x\ge\rho+1),
\qquad
\Pr(Q_w\le x)\le\Pr(H\le x)\quad(x\le\rho-1).
$$

Consequently $\Pr(|Q_w-\rho|\ge h)\le\Pr(|H-\rho|\ge h)$ for $h\ge1$.

**Proof.** Fix a positive integer $N$. Infinite divisibility of the Gamma law writes each $G_i$ as a sum of $N$ independent $\operatorname{Gamma}(\alpha/N,1)$ variables. Thus $Q_w$ has exactly the same distribution as a Gamma sum with shape $\alpha/N$ and the coefficient vector formed by repeating $w$ $N$ times. The coefficient cap is still one, the coefficient sum is $N\sigma$, and the mean is still $\rho$.

Lemma 3 compares this sum with $H_N$ having Laplace transform

$$
\mathbb E e^{-uH_N}
=(1+u)^{-\alpha\lfloor N\sigma\rfloor/N}
(1+r_Nu)^{-\alpha/N},
\qquad r_N=N\sigma-\lfloor N\sigma\rfloor\in[0,1).
$$

The second factor is interpreted as one when $r_N=0$. Since
$\alpha\lfloor N\sigma\rfloor/N\to\alpha\sigma=\rho$ and
$0\le\log(1+r_Nu)\le\log(1+u)$ for $u>0$, these transforms tend to $(1+u)^{-\rho}$, the transform of $H$.

One can also see the weak convergence without invoking a transform convergence theorem: for all sufficiently large $N$, $H_N$ is the sum of an independent Gamma variable of shape $\alpha\lfloor N\sigma\rfloor/N$ and rate one, and a nonnegative residual of mean $r_N\alpha/N\to0$. The first shape tends to $\rho>0$, so its law converges to $H$, and the residual tends to zero in probability by Markov's inequality. Thus $H_N$ converges in distribution to $H$.

Every real number is a continuity point of the Gamma CDF, including zero. Passing to the limit in the one-sided comparisons supplied by Lemma 3 proves the assertions. $\square$

## Proof of Theorem 1

Let $\lambda_i\ge0$ be the eigenvalues of $A$, with $\lambda_{\max}=\|A\|_2>0$, and put

$$
w_i=\lambda_i/\lambda_{\max},\qquad
\alpha=m/2,\qquad \rho=\alpha\mu.
$$

Rotational invariance of the standard Gaussian law and the identity $\chi_m^2/2\sim\operatorname{Gamma}(m/2,1)$ give

$$
\frac{T_m(A)}{\operatorname{tr}A}
\ \stackrel{d}{=}\ \frac{Q_w}{\rho}.
$$

The corresponding extremal coefficient vector in Lemma 3 is precisely the vector defining $B_\mu$, after multiplication by $\mu$, so

$$
T_m(B_\mu)\ \stackrel{d}{=}\ \frac{Q_{w^{\mathrm{ext}}}}{\rho}.
$$

Finally, if $H\sim\operatorname{Gamma}(\rho,1)$, then $H/\rho$ has the law of $X$. The hypothesis on $\varepsilon$ is exactly

$$
h:=\rho\varepsilon\ge1.
$$

Apply Lemma 3 to $Q_w$ and then Lemma 4 to $Q_{w^{\mathrm{ext}}}$. Dividing the variables and the deviation threshold by $\rho$ gives the full stated chain. $\square$

## Scope and relation to the auxiliary counterexamples

The argument works for every $m\ge1$, including $m=1$, every nonzero positive semidefinite matrix, every effective rank (integer or noninteger), and the stated endpoint $\varepsilon=2/(m\mu)$. Rank deficiency and zero padded coefficients are harmless. No estimate for an individual density with arbitrary augmentation indices is asserted.

The new point is the choice of transfers: the smaller augmented scale is always a minimum positive scale of the current distribution. General majorization paths need not have this property. Therefore the proof does not assert Hallman's disproved upper-mode Conjecture 1, and the auxiliary counterexample does not contradict the argument.

## References

1. **Hallman.** Eric Hallman, *Extremal bounds for Gaussian trace estimation*, arXiv:2411.15454v1 (2024), §5, Theorem 6 and Conjecture 3; Appendix A.1 for the coefficient derivative. [Primary text](https://arxiv.org/html/2411.15454v1).
2. **Roosta-Khorasani and Székely.** Farbod Roosta-Khorasani and Gábor J. Székely, *Schur properties of convolutions of gamma random variables*, Metrika **78** (2015), 997–1014, Appendix A, Theorem 4 and Lemma 5. [Primary arXiv text](https://arxiv.org/html/1601.04731v1); [DOI](https://doi.org/10.1007/s00184-015-0537-9).
3. **RA-12.** *Relative-error threshold for extremal Gaussian trace bounds*, retained canonical problem statement in OpenProblemsInNLA. [Canonical entry](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/randomized-and-low-rank-approximation/RA-12/README.md).
