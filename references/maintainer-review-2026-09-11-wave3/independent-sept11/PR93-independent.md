# Independent mathematical audit of PR #93

Date: 2026-09-11. Frozen head: `c797aee814c8bebe4452329c93f5d84fd9c41f1f`.
Snapshot: `/private/tmp/nla-review-wave3-artifacts/pr-93`.

**Verdict: mathematically verified for the complete canonical RA-12 target. No blocking gap or counterexample found.** The two probability comparisons hold for every permitted matrix, sample number and tolerance, including the stated endpoint. This conclusion comes from checking the proof and its external dependency, not from the manuscript's PASS labels. I did not consult the submitted independent-review report. This is an independent agent audit, not formal certification or external human peer review.

The audited mathematical files are `randomized-and-low-rank-approximation/RA-12/README.md`, `solution.md`, and `solution.tex` in the frozen snapshot. The preserved `references/stepaniants-ra12-2026-09-11/original-canonical-README.md` was also checked for target fidelity. No snapshot, checkout or public GitHub state was changed.

## 1. Target and normalization

The frozen README's lines 43–72 and the preserved original's lines 29–58 specify the same complete chain. Theorem 1, `solution.md:17–43` / `solution.tex:61–92`, retains it. There is no switch from two-sided to upper-tail error, no restriction to integer effective rank, and no restriction to positive definite matrices.

Independently diagonalize the real symmetric PSD matrix. If its eigenvalues are $\lambda_i$ and $\lambda_*=\|A\|_2>0$, Gaussian rotational invariance gives independent variables

$$
G_i=\frac12\sum_{j=1}^m \xi_{ji}^2
\sim\operatorname{Gamma}(m/2,1),
\qquad
T_m(A)=\frac2m\sum_i\lambda_iG_i.
$$

Writing $\alpha=m/2$, $w_i=\lambda_i/\lambda_*$ and $\rho=\alpha\sum_iw_i=\alpha\mu$, one obtains

$$
\frac{T_m(A)}{\operatorname{tr}A}=\frac{\sum_iw_iG_i}{\rho}.
$$

Thus the proof's normalization (`solution.md:232–255`, TeX 362–390) has the correct factor of two. The capped vector has $\lfloor\mu\rfloor$ ones and fractional remainder, giving exactly $T_m(B_\mu)=Q_{w^{\rm ext}}/\rho$ in distribution. A Gamma variable of shape $\rho$ and rate one divided by $\rho$ has shape and **rate** both $\rho$, as the target requires. Finally $\rho\varepsilon\ge1$ is exactly $\varepsilon\ge2/(m\mu)$.

These calculations do not require any coupling between estimators or a common matrix dimension.

## 2. Lemma 2: the new mode bound

Location: `solution.md:51–113`; `solution.tex:108–182`.

I independently checked the convolution argument. For positive shapes $r_i$ and scales $w_i$, put $R=\sum_i r_i>1$ and $k(t)=\sum_i r_i e^{-t/w_i}$. The Laplace-transform relation

$$
-L'(u)=L(u)\sum_i\frac{r_iw_i}{1+w_i u}
$$

indeed gives $xf(x)=(k*f)(x)$. There is no rate/scale inversion: the integral of $k$ is $M=\sum_i r_iw_i$, the correct mean.

The density has a positive interior global maximum. For example, its simplex convolution representation gives an upper bound $C x^{R-1}e^{-x/w_+}$, and its small-$x$ behavior is a positive constant times $x^{R-1}$. Hence it vanishes both at zero and infinity. Its smoothness on the positive half-line gives $f'(z)=0$ at an interior global maximum $z$.

Differentiating the **kernel**, rather than requiring bounded $f'$ near zero, yields

$$
f(x)+xf'(x)=k(0)f(x)+\int_0^x k'(t)f(x-t)\,dt.
$$

This remains valid for $1<R<2$, when the derivative of the density at zero need not be finite. With the zero extension of $f$ and $v(t)=1-f(z-t)/f(z)$, global maximality gives $0\le v\le1$. At $z$ the two equations become

$$
\int_0^\infty k(t)v(t)\,dt=M-z,
\qquad
\int_0^\infty[-k'(t)]v(t)\,dt=1.
$$

The second constant is exactly one: the convolution integral of $-k'$ against $f(z-t)/f(z)$ is $k(0)-1$, which is subtracted from $\int(-k')=k(0)$. There is no missing shape factor or boundary term.

The pointwise bounds $w_-(-k')\le k\le w_+(-k')$ therefore give $w_-\le M-z\le w_+$. The proposed mode interval follows. This part needs only a global mode, not strict log-concavity or any unproved mode-location assertion. Its integral manipulations involve bounded $v$ and integrable kernels.

## 3. External unimodality dependency

Location: `solution.md:47,175`; `solution.tex:97–103,263–264`.

I checked [Roosta-Khorasani–Székely, Appendix A, Theorem 4 and Lemma 5](https://arxiv.org/html/1601.04731v1#A1), including the [published article's appendix](https://link.springer.com/article/10.1007/s00184-015-0537-9). The theorem covers independent Gamma variables with arbitrary positive shapes and rates, with nonnegative coefficients; it is not restricted to equal shapes or shapes at least one. Lemma 5 supplies the positive-half-line regularity and zero-boundary behavior used here. The publication is Metrika 78, 997–1014 (2015), matching the manuscript's citation.

Only unimodality and the stated regularity are used. The proof does not use the source's separate mode-monotonicity lemma or infer strict concavity merely from a unique maximum. The external theorem is taken as established published mathematics; I checked its exact hypotheses and applicability rather than reconstructing its earlier cited proof.

## 4. Lemma 3: transfer path, derivative and tail directions

Location: `solution.md:117–197`; `solution.tex:187–308`.

The transfer selection is the decisive valid step. Among strictly fractional coefficients choose a smallest $b$, and another $a\ge b$. Every other positive coefficient is either one or a fractional coefficient at least $b$. Along $a+t,b-t$, with $0\le t<\min(1-a,b)$, the decreasing coefficient remains the minimum positive scale of the **whole** sum. Ties among minima do not invalidate this property.

The augmented sum $Y_t=Q_t+(a+t)E_1+(b-t)E_2$ has mean $\rho+a+b$ and total shape greater than two. Its maximal scale is at most one and its minimal scale is $b-t$. Lemma 2 consequently gives

$$
\rho-1\le \rho+a+b-1\le z_t
\le \rho+a+b-(b-t)=\rho+a+t\le\rho+1.
$$

Unimodality now yields $g_t'\ge0$ below $\rho-1$ and $g_t'\le0$ above $\rho+1$. This does not apply an invalid mode bound to arbitrary augmentation indices: it uses the minimum-scale property just proved.

I separately differentiated the CDF transform. If $L_t$ is the transform of $Q_t$, then

$$
\partial_t\log L_t
=-\frac{\alpha u}{1+(a+t)u}
 +\frac{\alpha u}{1+(b-t)u}
=\frac{\alpha(a-b+2t)u^2}
 {(1+(a+t)u)(1+(b-t)u)}.
$$

Dividing by $u$ for the CDF transform gives exactly the submitted identity

$$
\partial_tF_{Q_t}(x)=\alpha(a-b+2t)g_t'(x).
$$

The sign is correct. The lower CDF increases, so the lower tail becomes larger after concentration of the weights. The CDF above the upper threshold decreases, so the upper survival probability also becomes larger. The augmented density vanishes at zero, so inverse transformation of $uL_{Y_t}$ introduces no boundary mass. The attribution agrees with [Hallman, Appendix A.1](https://arxiv.org/html/2411.15454v1#A1.SS1).

Differentiation is valid on any compact subinterval before the decreasing weight reaches zero. More explicitly, the joint scaled-Gamma density and its scale derivatives are dominated on the bounded integration simplex $\sum y_i\le x$ by a constant times $\prod_i y_i^{\alpha-1}$ when varying scales stay bounded away from zero. This establishes differentiability of the CDF for any $\alpha>0$. The pointwise derivative identity can then be obtained by the submitted Laplace calculation and uniqueness.

At the endpoint of a transfer, couple all variables using fixed independent $G_i$. The weighted sum converges almost surely as coefficients converge. The limit has at least one positive coefficient because its sum remains $\sigma>0$, and therefore is atomless. The CDF inequalities pass to the endpoint, including a zero coefficient. At least one fractional coefficient disappears at every transfer; finitely many transfers produce precisely the capped vector. No infinite transfer process is being assumed.

The comparison interval depends only on $\rho$ and the cap one. It does not depend on dimension, the number of fractional entries, the smallest nonzero eigenvalue, or a lower bound on $\alpha$.

## 5. Lemma 4: passage to a single Gamma law

Location: `solution.md:201–228`; `solution.tex:313–358`.

The Gamma subdivision is correct. Replacing each $G_i$ by a sum of $N$ independent Gamma variables of shape $\alpha/N$ preserves its law; repeating each coefficient $N$ times changes the coefficient sum to $N\sigma$ while preserving mean $\rho$. Lemma 3 was proved for **every** positive shape, so it remains applicable as $\alpha/N$ tends to zero.

For each finite $N$ its extremal comparator is distributed as

$$
H_N=Z_N+r_NV_N,
\quad Z_N\sim\operatorname{Gamma}
  \left(\alpha\lfloor N\sigma\rfloor/N,1\right),
\quad V_N\sim\operatorname{Gamma}(\alpha/N,1),
$$

with independence and $r_N=N\sigma-\lfloor N\sigma\rfloor$. If the first shape is zero for an early $N$, the first term is simply absent; the proof's elementary convergence argument explicitly uses sufficiently large $N$, when it is positive. If $r_N=0$, the second term vanishes.

The first shape converges to $\rho>0$ and $\mathbb E(r_NV_N)\le\alpha/N\to0$. Thus $H_N$ converges in distribution to $H\sim\operatorname{Gamma}(\rho,1)$. The comparison thresholds stay fixed at $\rho\pm1$ throughout. Since the Gamma CDF is continuous at every real number, including zero, both one-sided comparisons pass to the limit. No uniform-in-$x$ convergence or interchange of an extremum with a limit is needed.

This establishes a bound by the Gamma law. It does not require that, for noninteger $\mu$ and fixed integer $m$, this limiting law be realized by an actual Gaussian trace estimator of some matrix. The manuscript correctly claims no such realization.

## 6. Edge cases, strength and completion

- **Rank one or integer effective rank:** the capped estimator itself is Gamma when $\mu$ is an integer. In particular rank-one inputs give equality throughout; this is consistent with the theorem.
- **Rank deficiency:** zero eigenvalues contribute no random term. Deleting or adding zero coefficients leaves all arguments unchanged.
- **$m=1$:** $\alpha=1/2$ is allowed, and the auxiliary augmented law still has total shape greater than two. No hidden $m\ge2$ or log-concavity assumption appears.
- **$\rho\le1$ or $\varepsilon\ge1$:** the lower cutoff is nonpositive whenever relevant. Every nonzero weighted Gamma sum and the limiting Gamma variable are strictly positive almost surely, so those lower-tail probabilities are zero. At cutoff zero there is no atom.
- **Equality at $\varepsilon=1/\rho$:** the mode bounds are non-strict, the derivative signs include the boundary, and all distributions are continuous. The endpoint is proved, not obtained by silently restricting to larger tolerances.
- **Strict versus non-strict tails:** every final sum has an absolutely continuous nondegenerate law, so replacing $>$ by $\ge$ or $<$ by $\le$ at finite cutoffs changes no probability.
- **Combining tails:** $h=\rho\varepsilon\ge1>0$, so $\{Q\le\rho-h\}$ and $\{Q\ge\rho+h\}$ are disjoint; summing their bounds yields exactly the absolute-deviation probability.
- **Uniformity:** the proof applies separately to every finite spectrum with the same universal threshold formula. The subdivision dimensions may grow, but their thresholds do not.
- **Optimality versus sufficiency:** [Hallman, Theorem 6 and Conjecture 3](https://arxiv.org/html/2411.15454v1#S5), ask for a sufficient threshold no larger than $2/(m\mu)$. The proof establishes that assertion; it does not prove the smallest possible threshold. Frozen README line 18 explicitly disclaims optimality. No sharpness argument is missing from the stated target.
- **Auxiliary counterexamples:** the proof establishes only the modes of the deliberately chosen augmented sums, not the universal arbitrary-index mode or inflection claims. Consequently the retained Colbrook auxiliary counterexamples do not contradict this proof.

The same mathematical statements and arguments appear in `solution.tex`; the corresponding line ranges above were checked. No material formula or hypothesis discrepancy was found between Markdown and TeX.

## Final assessment

The complete canonical probability chain follows from independently checked Lemmas 2–4 and the exact Gaussian-to-Gamma normalization. No additional proof repair is required for RA-12 at the reviewed head. The appropriate mathematical outcome is an affirmative resolution of this target, with the repository's usual qualification that verification is independent agent review rather than external peer review or formal certification. Numerical experiments would neither strengthen nor replace the analytic verification carried out here, so no sampling-based evidence is used.
