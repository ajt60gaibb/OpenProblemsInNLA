# MI-27: The logarithmic commutator inequality with sharp constant one

**Author:** Sidney Holden  
**Affiliation:** Center for Computational Biology, Flatiron Institute, Simons Foundation.


**12 September 2026. Complete analytic proof using a published relative-entropy identity.**

## 1. Result

For every integer $n\ge1$ and positive definite $A,B\in\mathbb C^{n\times n}$ with $\operatorname{tr}(A+B)=1$, put $a=\operatorname{tr}A$ and $b=\operatorname{tr}B$. Then

$$
\boxed{\|[B,\log(A+B)]\|_1\le-a\log a-b\log b.}
$$

The coefficient **one is optimal**, even for strictly positive definite $2\times2$ matrices. This is the precise coefficient asked for in [MI-27][MI27].

All logarithms are natural; $[X,Y]=XY-YX$; $\|X\|_1=\operatorname{tr}\sqrt{X^*X}$ is the full trace norm; and $\|X\|_\infty$ is the operator norm. Write $h(b)=-a\log a-b\log b$, with $a+b=1$. A density matrix is positive semidefinite and has trace one.

The only non-elementary input below is Frenkel's relative-entropy integral formula, in the form given by Hirche and Tomamichel. The rest of the proof is given explicitly. Numerical calculations are not used to prove the universal assertion.

## 2. The positive-part unitary estimate

### Elementary commutator lemma

For $X\ge0$ and $0\le Q\le I$,

$$
\|[X,Q]\|_1\le\operatorname{tr}X.
$$

Indeed, $R=2Q-I$ is a contraction, so

$$
\|[X,Q]\|_1=\tfrac12\|XR-RX\|_1
\le\tfrac12(\|XR\|_1+\|RX\|_1)
\le\|X\|_1\|R\|_\infty\le\operatorname{tr}X.
$$

### Uniform Lipschitz lemma

For density matrices $\rho,\sigma$ and $\gamma\ge1$, define

$$
E_\gamma(\rho\Vert\sigma)=\operatorname{tr}(\rho-\gamma\sigma)_+.
$$

Here $M_+$ is the positive part of the Hermitian matrix $M$. Let $H=H^*$, $U_t=e^{itH}$ and $\sigma_t=U_t\sigma U_t^*$. Then, for all real $s,t$,

$$
\begin{aligned}
|E_\gamma(\rho\Vert\sigma_t)-E_\gamma(\rho\Vert\sigma_s)|
 &\le |t-s|\|H\|_\infty,\\
|E_\gamma(\sigma_t\Vert\rho)-E_\gamma(\sigma_s\Vert\rho)|
 &\le |t-s|\|H\|_\infty.
\end{aligned}
$$

**Proof, including eigenvalue crossings.** The variational formula

$$
\operatorname{tr}M_+=\max_{0\le Q\le I}\operatorname{tr}QM
$$

implies $|\operatorname{tr}M_+-\operatorname{tr}N_+|\le\|M-N\|_1$. Therefore $f(t)=\operatorname{tr}M(t)_+$, where $M(t)=\rho-\gamma\sigma_t$, is locally Lipschitz and absolutely continuous on every compact interval.

At a point where $f$ is differentiable, fix the positive spectral projection $Q_t=\mathbf1_{(0,\infty)}(M(t))$. It maximizes the variational formula, commutes with $M(t)$, and satisfies

$$
f(t+u)\ge\operatorname{tr}Q_tM(t+u)
=f(t)+u\operatorname{tr}Q_tM'(t)+o(|u|).
$$

Taking $u\to0$ from both sides gives $f'(t)=\operatorname{tr}Q_tM'(t)$. No derivative of $Q_t$ is assumed. Since

$$
[\rho,Q_t]=\gamma[\sigma_t,Q_t],
$$

we obtain

$$
\begin{aligned}
f'(t)
&=-i\gamma\operatorname{tr}Q_t[H,\sigma_t]\\
&=-i\gamma\operatorname{tr}H[\sigma_t,Q_t]
=-i\operatorname{tr}H[\rho,Q_t].
\end{aligned}
$$

Thus $|f'(t)|\le\|H\|_\infty\|[\rho,Q_t]\|_1\le\|H\|_\infty$ almost everywhere. Integrating proves the first estimate. The second follows from

$$
E_\gamma(\sigma_t\Vert\rho)=E_\gamma(\sigma\Vert U_t^*\rho U_t)
$$

and the first estimate with generator $-H$.

The decisive point is the cancellation of $\gamma$. The generic perturbation estimate for the second argument does not provide this cancellation.

## 3. A positive integral with exactly the required mass

Let

$$
D(\rho\Vert\sigma)=\operatorname{tr}\rho(\log\rho-\log\sigma),\qquad
S(\rho)=-\operatorname{tr}\rho\log\rho.
$$

Frenkel's Theorem 6, equivalently Hirche–Tomamichel's Corollary 2.3, equation (2.22), gives

$$
D(\rho\Vert\sigma)=\int_1^\infty\left[
\frac{E_\gamma(\rho\Vert\sigma)}{\gamma}
+\frac{E_\gamma(\sigma\Vert\rho)}{\gamma^2}
\right]d\gamma. \tag{1}
$$

This is an identity for the **ordinary Umegaki relative entropy**, including noncommuting matrices; see [Frenkel][F] and [Hirche–Tomamichel][HT].

For $\alpha\in(0,1)$, $\beta=1-\alpha$, apply (1) to $\rho$ and $M=\alpha\rho+\beta\sigma$. For $1\le v<1/\alpha$,

$$
E_v(\rho\Vert M)=(1-\alpha v)
E_{\beta v/(1-\alpha v)}(\rho\Vert\sigma),
$$

and this positive part vanishes for $v\ge1/\alpha$. Also,

$$
E_v(M\Vert\rho)=\beta E_{(v-\alpha)/\beta}(\sigma\Vert\rho).
$$

The substitutions $v=\gamma/(\beta+\alpha\gamma)$ and $v=\alpha+\beta\gamma$, respectively, yield

$$
D(\rho\Vert\alpha\rho+\beta\sigma)=
\int_1^\infty\left[
\frac{\beta^2 E_\gamma(\rho\Vert\sigma)}{\gamma(\beta+\alpha\gamma)^2}
+\frac{\beta^2 E_\gamma(\sigma\Vert\rho)}{(\alpha+\beta\gamma)^2}
\right]d\gamma. \tag{2}
$$

Define the weighted entropy difference

$$
\begin{aligned}
\chi_{a,b}(\rho,\sigma)
&=S(a\rho+b\sigma)-aS(\rho)-bS(\sigma)\\
&=aD(\rho\Vert a\rho+b\sigma)+bD(\sigma\Vert a\rho+b\sigma).
\end{aligned}
$$

Applying (2) to both terms and collecting coefficients gives

$$
\boxed{
\chi_{a,b}(\rho,\sigma)=ab\int_1^\infty\left[
\frac{E_\gamma(\rho\Vert\sigma)}{\gamma(b+a\gamma)}
+\frac{E_\gamma(\sigma\Vert\rho)}{\gamma(a+b\gamma)}
\right]d\gamma.} \tag{3}
$$

For example, the first coefficient simplifies to

$$
\frac{ab^2}{\gamma(b+a\gamma)^2}
+\frac{ba^2}{(b+a\gamma)^2}
=\frac{ab}{\gamma(b+a\gamma)}.
$$

The two nonnegative kernels have masses

$$
ab\int_1^\infty\frac{d\gamma}{\gamma(b+a\gamma)}=-a\log a,
\qquad
ab\int_1^\infty\frac{d\gamma}{\gamma(a+b\gamma)}=-b\log b. \tag{4}
$$

For the first integral, use the primitive $a\log(\gamma/(b+a\gamma))$; for the second, exchange $a,b$. Since $0\le E_\gamma\le1$, all integrals in (3) converge absolutely.

## 4. The entropy estimate and trace-norm duality

Set $\rho=A/a$, $\sigma=B/b$, and

$$
T_t=A+e^{itH}Be^{-itH}=a\rho+b\sigma_t.
$$

Unitary invariance of entropy shows that

$$
S(T_t)-S(T_0)=\chi_{a,b}(\rho,\sigma_t)-\chi_{a,b}(\rho,\sigma).
$$

Apply the Lipschitz lemma to each of the two positive-part terms in (3), and integrate using (4). The result is

$$
|S(T_t)-S(T_0)|\le |t|\|H\|_\infty h(b). \tag{5}
$$

This uses **finite differences**, not differentiation under an improper integral. The positive-part functions need not be differentiable at every time.

Now put $T=A+B>0$. Since $T'_0=i[H,B]$ and $\operatorname{tr}T'_0=0$, differentiation of the trace of $-T_t\log T_t$ gives

$$
\left.\frac{d}{dt}S(T_t)\right|_{t=0}
=-i\operatorname{tr}[H,B]\log T
=-i\operatorname{tr}H[B,\log T].
$$

Divide (5) by $|t|$ and let $t\to0$. The matrix $K=-i[B,\log T]$ is Hermitian, and therefore

$$
|\operatorname{tr}HK|\le\|H\|_\infty h(b)
\quad\text{for every Hermitian }H.
$$

Choose $H=\operatorname{sign}K$, with zero on its kernel. Then $\|H\|_\infty\le1$ and

$$
\operatorname{tr}HK=\operatorname{tr}|K|=\|[B,\log T]\|_1.
$$

This proves the asserted coefficient-one inequality for all matrix sizes and all strictly positive definite inputs.

## 5. Optimality with both matrices strictly positive definite

This family comes from Theorem 2 of the supplied MI-27 findings; an unchanged copy is included in `provenance/input_MI27_result.md`.

For $0<t<1/2$, let

$$
T_t=\begin{pmatrix}1-t&0\\0&t\end{pmatrix},\qquad
d_t=(1-2t^2)t(1-t),
$$

$$
B_t=t^2T_t+d_t\begin{pmatrix}1&1\\1&1\end{pmatrix},\qquad A_t=T_t-B_t.
$$

With $u_t=(\sqrt t,\sqrt{1-t})^{\mathsf T}$ and $P_t=u_tu_t^*$,

$$
B_t=T_t^{1/2}\bigl(t^2I+(1-2t^2)P_t\bigr)T_t^{1/2}.
$$

The middle factor has eigenvalues $t^2$ and $1-t^2$, both strictly between zero and one. Thus $A_t,B_t>0$ and $\operatorname{tr}(A_t+B_t)=1$. Directly,

$$
\det A_t=\det B_t=t^3(1-t)(1-t^2)>0.
$$

Writing $b_t=\operatorname{tr}B_t$, we have

$$
b_t=t^2+2d_t,\qquad
\|[B_t,\log T_t]\|_1=2d_t\log\frac{1-t}{t}.
$$

The commutator has two equal singular values, each $d_t\log((1-t)/t)$. As $t\downarrow0$, $d_t\sim t$, $b_t\sim2t$, and

$$
2d_t\log\frac{1-t}{t}\sim2t\log(1/t),\qquad
h(b_t)\sim2t\log(1/t).
$$

Here the second equivalence follows from $h(x)=x\log(1/x)+x+O(x^2)$. Consequently,

$$
\boxed{\lim_{t\downarrow0}
\frac{\|[B_t,\log(A_t+B_t)]\|_1}{h(\operatorname{tr}B_t)}=1.}
$$

Every coefficient $c<1$ therefore fails for sufficiently small positive $t$ within the original strictly positive definite class.

## 6. Two consequences

For normalized skew divergence

$$
\mathrm{SD}_\alpha(\rho\Vert\sigma)=
\frac{D(\rho\Vert\alpha\rho+(1-\alpha)\sigma)}{-\log\alpha},
$$

the two kernels in (2) have masses $-\log\alpha-(1-\alpha)$ and $1-\alpha$. The same argument therefore yields

$$
|\mathrm{SD}_\alpha(\rho\Vert U_t\sigma U_t^*)
-\mathrm{SD}_\alpha(\rho\Vert\sigma)|\le |t|\|H\|_\infty.
$$

Also, for every positive definite trace-one $T$ and every orthogonal projection $P$ of arbitrary rank, the pack's projection assertion now follows:

$$
\|[T^{1/2}PT^{1/2},\log T]\|_1\le h(\operatorname{tr}TP).
$$

To see this, set $K_\varepsilon=\varepsilon I+(1-2\varepsilon)P$, $B_\varepsilon=T^{1/2}K_\varepsilon T^{1/2}$ and $A_\varepsilon=T-B_\varepsilon$. Apply the proved theorem and let $\varepsilon\downarrow0$. The sum $T$ and its logarithm stay fixed. The PDF includes the converse projection reduction as well, with the varying-trace Jensen step made explicit.

## 7. Scope and reproducibility

`verification/verify.py` checks nine identities exactly with SymPy and performs deterministic numerical consistency tests of the positive-part estimate, the published and derived integral formulas, finite-time entropy bounds, trace-norm duality, and entropy derivatives. It also evaluates the sharpness family at high precision. Generalized eigenvalues are supplied as quadrature breakpoints. The full results, software versions, tolerances, and seed are included.

The analytic proof does not depend on those tests. This write-up is not an independently refereed article or a proof-assistant formalization. No historical publication-priority claim is made. The PDF and LaTeX contain the expanded proof and appendices, and `provenance.md` distinguishes the contributions of the supplied pack from the upper-bound argument.

## References

**Frenkel.** Péter E. Frenkel, *Integral formula for quantum relative entropy implies data processing inequality*, Quantum **7**, 1102 (2023), Theorem 6; arXiv:2208.12194v4. DOI: 10.22331/q-2023-09-07-1102.

**Hirche–Tomamichel.** Christoph Hirche and Marco Tomamichel, *Quantum Rényi and f-divergences from integral representations*, Communications in Mathematical Physics **405**, 208 (2024), Corollary 2.3, equation (2.22), and Proposition 2.9; arXiv:2306.12343v3. DOI: 10.1007/s00220-024-05087-3.

**Historical formulation.** K. M. R. Audenaert and F. Kittaneh, *Problems and Conjectures in Matrix and Operator Inequalities*, arXiv:1201.5232v3 (2012), Section 6, Conjecture 4, equation (26), and the sentence proposing coefficient one.

**Coefficient-two approach.** K. M. R. Audenaert, *Quantum Skew Divergence*, Journal of Mathematical Physics **55**, 112202 (2014), Section 8; arXiv:1304.5935.

**Supplied findings.** `OpenProblemsInNLA_matrix_proof_checkpoint_2026-09-12/MI-27/result.md`, Theorems 1–2: projection equivalence and strictly positive definite sharpness family. The original findings explicitly did not prove the universal upper bound.

[MI27]: https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/matrix-inequalities-and-norms/MI-27
[F]: https://arxiv.org/html/2208.12194
[HT]: https://arxiv.org/html/2306.12343v3#S2.SS3
