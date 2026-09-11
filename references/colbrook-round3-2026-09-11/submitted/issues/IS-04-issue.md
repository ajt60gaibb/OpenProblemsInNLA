### Affected entry

[IS-04](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/eigenvalues-and-inverse-problems/IS-04/README.md), the main mathematical target. Statement checked on 11 September 2026 against the repository's 10 September audit.

### Correction or result

**Proposed status: Partially resolved (unchanged).** For every odd prime $p\geq13$, the explicit construction below gives a real $p^2\times p^2$ sign matrix with
$$
\kappa_2(A_p)\leq\frac{p+2+3\sqrt p}{p-2-3\sqrt p}=1+O(p^{-1/2}).
$$
For every prime $p\geq361$, the bound is at most $210/151<\sqrt2$.

**This does not settle IS-04.** Only the odd orders $n=p^2$ are covered; the assertion for every dimension remains unproved here. The value of this report is an explicit infinite family, not another nonconstructive proof that $h(n)\to1$, which is already known.

The same construction proposes an affirmative answer to the distinct related Problem 13 in Alexeev–Jasper–Mixon, Section 6 (an explicit infinite odd-order family below $\sqrt2$). It should not be presented as a full resolution of the repository's Problem 12 / IS-04 target, or assigned a new problem ID merely to increase the count.

No symmetry or cyclic-circulant restriction is assumed by IS-04. The construction is convolution over $\mathbb F_p^2$, with unrestricted real sign entries, so it is in the stated matrix class.

### Evidence

The self-contained manuscript is included in full below. Main locator: Theorem 1; explicit kernel: (3)–(5); exact transform: Lemma 2; imported mixed Weil bound and its specialization: Section 4; condition-number estimate: Section 5. The classical character-sum theorem is explicitly cited, not claimed as new.

The matching PDF is named `IS-04-explicit-odd-family-partial.pdf`. Reproducible supporting code is supplied separately in `verification-support.zip`; tests do not establish the theorem by themselves.

**Verification and provenance:** this is an AI-generated proposed argument, not an independently refereed or formally verified result. No priority claim is made. The complete argument and precise source locators are provided so that the claim can be checked.

### Rating implications, if any

No change to the existing difficulty or importance rating is proposed. The all-dimensions question remains the surviving open target; record the explicit family as partial progress only.

## Self-contained manuscript

### 1. Result and its precise scope

Repository problem **IS-04** asks whether every order admits a real sign matrix with spectral condition number at most two.[^repo] The construction below is **partial progress for that problem**: it covers the infinite sequence of odd orders $n=p^2$, not all dimensions. It also proposes an affirmative answer to the distinct, related **Problem 13** in the cited paper of Alexeev, Jasper, and Mixon, which asks for an explicit infinite odd-order family with condition number below $\sqrt2$.[^ajm]

**Theorem 1 (explicit prime-square family).** For each odd prime $p\geq13$, the construction in Section 2 produces a real matrix $A_p\in\{-1,1\}^{p^2\times p^2}$ satisfying
$$
\kappa_2(A_p)
\leq\frac{p+2+3\sqrt p}{p-2-3\sqrt p}. \tag{1}
$$
In particular,
$$
\kappa_2(A_p)=1+O(p^{-1/2})=1+O(n^{-1/4}),\qquad n=p^2.
$$
For every prime $p\geq361$,
$$
\kappa_2(A_p)\leq\frac{210}{151}<\sqrt2. \tag{2}
$$
No search over sign matrices or random choices is used. The construction uses arithmetic in $\mathbb F_p$ and the quadratic character. The matrices are developed over the additive group $\mathbb F_p^2$; they need not be symmetric or circulant over the cyclic group of order $p^2$. Neither additional restriction is part of IS-04 or the related Problem 13.

The character-sum estimate used in the proof is classical and is explicitly isolated in Section 4. It is not claimed as a new result.

### 2. The construction

Let $\chi:\mathbb F_p\to\{-1,0,1\}$ be the quadratic character, with $\chi(0)=0$. Choose a nonsquare $d\in\mathbb F_p^\times$, for example the least positive nonsquare in the usual integer representatives, and put
$$
\epsilon=\chi(-1),\qquad Q(x,y)=x^2-dy^2,
\qquad c(x,y)=\chi(Q(x,y)).
$$
The quadratic form is anisotropic: $Q(x,y)=0$ only at $(0,0)$. Thus $c$ is a sign away from the origin and is zero there.

Define the parabola
$$
\Gamma(t)=(2dt,1+dt^2),
$$
and its quadratic-residue subset
$$
S=\{\Gamma(t):t\in\mathbb F_p^\times,\ \chi(t)=1\}. \tag{3}
$$
The parametrization is injective because $2d\ne0$. Its image avoids the origin. Moreover,
$$
Q(\Gamma(t))=-d(1-dt^2)^2.
$$
Since $d$ is a nonsquare, $1-dt^2$ never vanishes. Consequently
$$
c(\Gamma(t))=\chi(-d)=-\epsilon
\quad\text{for every }t\in\mathbb F_p.
$$
Thus the kernel
$$
a(x,y)=c(x,y)+\epsilon\,\mathbf1_{\{(0,0)\}}(x,y)
       +2\epsilon\,\mathbf1_S(x,y) \tag{4}
$$
takes values only in $\{-1,1\}$: it fills the origin with $\epsilon$ and changes the selected entries from $-\epsilon$ to $\epsilon$.

Index both rows and columns by $G=\mathbb F_p^2$, in lexicographic order if a concrete indexing is needed, and set
$$
A_p(g,h)=a(g-h). \tag{5}
$$
Equations (3)–(5) specify every entry deterministically. The flip-set cardinality is immediate from the number of nonzero quadratic residues:
$$
|S|=\frac{p-1}{2}. \tag{6}
$$

### 3. Exact Fourier transform of the unmodified kernel

Write $e_p(s)=\exp(2\pi i s/p)$ and use the unnormalized transform
$$
\widehat f(u,v)=\sum_{x,y\in\mathbb F_p}f(x,y)e_p(ux+vy).
$$

**Lemma 2 (flat nontrivial Fourier coefficients).**
$$
\widehat c(0,0)=0,
\qquad
\widehat c(u,v)=-\epsilon p\,\chi(u^2-d^{-1}v^2)
\quad\text{for }(u,v)\ne(0,0). \tag{7}
$$
In particular, all nontrivial Fourier coefficients have modulus $p$.

*Proof.* Let $\tau=\sum_s\chi(s)e_p(s)$ be the quadratic Gauss sum. The identities
$$
\tau^2=\epsilon p,\qquad
\chi(s)=\tau^{-1}\sum_{r\ne0}\chi(r)e_p(rs)
$$
follow from the usual change-of-variable and orthogonality calculations for quadratic Gauss sums. Completing squares gives, for $r\ne0$,
$$
\begin{aligned}
&\left(\sum_x e_p(rx^2+ux)\right)
\left(\sum_y e_p(-dry^2+vy)\right)\\
&\hspace{15mm}=-p\,e_p\left(-\frac{u^2-d^{-1}v^2}{4r}\right).
\end{aligned}
$$
Indeed, the product of the character factors is $\chi(-d)=-\epsilon$, and the product of the Gauss sums is $\tau^2=\epsilon p$.

Put $R=u^2-d^{-1}v^2$. Inserting the character expansion gives
$$
\widehat c(u,v)=-\frac p\tau\sum_{r\ne0}\chi(r)e_p(-R/(4r)).
$$
At $(u,v)=(0,0)$ the last character sum is zero. Otherwise $R\ne0$, since $d^{-1}$ is also a nonsquare. Substitute $r^{-1}$ for $r$ and apply the one-dimensional Gauss identity. The result is
$$
\widehat c(u,v)=-p\chi(-R/4)=-\epsilon p\chi(R).
$$
This proves (7). $\square$

### 4. The imported character-sum bound

We use the following special case of the classical mixed Weil estimate:
$$
\left|\sum_{t\in\mathbb F_p}\chi(t)e_p(\alpha t+\beta t^2)\right|
\leq2\sqrt p
\quad\text{if }(\alpha,\beta)\ne(0,0). \tag{8}
$$
Here $p$ is odd and $\chi$ is quadratic, with $\chi(0)=0$.

The constant can be checked through the standard rank-one formulation.[^weil] On the projective line remove zero and infinity. Tensor the Kummer sheaf for $\chi(t)$ with the Artin–Schreier sheaf for $e_p(\alpha t+\beta t^2)$. It has rank one and weight zero. Its nontrivial tame ramification at zero prevents geometric triviality. Its only Swan contribution is at infinity and equals $m=\deg(\alpha t+\beta t^2)\leq2<p$. Thus $H_c^0=H_c^2=0$, and the Euler–Poincaré formula gives $\dim H_c^1=m\leq2$. The trace formula and the weight bound on $H_c^1$ give (8). Omitting zero from the sheaf domain agrees with the zero summand in (8).

This paragraph only verifies the specialization and constant in an established theorem; the underlying Weil/Deligne estimate is an external input.

### 5. Fourier control of the flips and proof of Theorem 1

The indicator of the nonzero quadratic residues is $(1+\chi(t)-\mathbf1_{\{0\}}(t))/2$. Therefore, for a nonzero frequency $(u,v)$,
$$
\begin{aligned}
2\widehat{\mathbf1_S}(u,v)
=e_p(v)\bigg(&\sum_t e_p(2du\,t+dv\,t^2)\\
&+\sum_t\chi(t)e_p(2du\,t+dv\,t^2)-1\bigg).
\end{aligned} \tag{9}
$$
The first sum has modulus $\sqrt p$ when $v\ne0$, by completing a square; it is zero when $v=0$ and $u\ne0$. Since $2d$ and $d$ are nonzero, the additive polynomial in (9) is nonconstant. Equation (8) gives
$$
\left|2\widehat{\mathbf1_S}(u,v)\right|\leq3\sqrt p+1.
$$
Using (4) and Lemma 2,
$$
|\widehat a(u,v)-\widehat c(u,v)|\leq2+3\sqrt p,
\qquad (u,v)\ne(0,0). \tag{10}
$$
The zero frequency is not estimated by a triangle inequality. It is exactly corrected:
$$
\widehat a(0,0)=\widehat c(0,0)+\epsilon+2\epsilon|S|
=0+\epsilon+\epsilon(p-1)=\epsilon p. \tag{11}
$$

The normalized characters of the finite abelian group $G$ form an orthonormal basis. In this basis, convolution (5) is diagonal, with eigenvalues $\widehat a(u,v)$, up to the immaterial frequency-sign convention. Thus $A_p$ is normal and its singular values are exactly $|\widehat a(u,v)|$. Equations (7), (10), and (11) imply
$$
p-2-3\sqrt p\leq\sigma_{\min}(A_p)
\leq\sigma_{\max}(A_p)\leq p+2+3\sqrt p.
$$
The lower bound is positive for $p\geq13$: the expression increases there, and at $p=13$ positivity follows from $11^2>9\cdot13$. This proves (1).

For $p\geq361$, monotonicity of $2p^{-1}+3p^{-1/2}$ gives
$$
r_p:=\frac{2+3\sqrt p}{p}\leq\frac{59}{361}.
$$
Therefore
$$
\frac{1+r_p}{1-r_p}\leq\frac{420}{302}
=\frac{210}{151}<\sqrt2,
$$
where the last inequality is exact: $210^2=44100<45602=2\cdot151^2$. Since there are infinitely many primes beyond a fixed bound, (2) yields an explicit infinite family of odd orders. $\square$

### 6. Reproducibility and what remains open

The accompanying generator constructs the $p\times p$ kernel, not the potentially enormous $p^2\times p^2$ dense matrix. A two-dimensional discrete Fourier transform gives the complete list of singular values through their absolute values. Dense construction is included only for small orders and is guarded by a memory limit.

The verification code checks the sign property, the constant sign along the parabola, flip-set membership, (6), and the zero-frequency identity with exact integers. It checks (7), (8), and the singular-value bounds numerically on a specified list of primes, and compares the convolution formula against a dense singular-value decomposition at small sizes. The character-sum theorem, not the finite numerical sample, is what establishes the uniform bound.

The family does not include every odd order, much less every dimension. No claim about the exact supremum in IS-04 follows from an infinite subsequence. The all-order assertion remains unresolved by this manuscript. The result also does not determine the optimal all-order decay exponent from IS-05.

This is an AI-generated proposed construction and argument, prepared for review on 11 September 2026. It has not been independently refereed or formally verified, and no priority claim is made. For IS-04 the appropriate report is **partial progress**, leaving its existing **Partially resolved** status unchanged. The proposed affirmative answer concerns the related Problem 13 in the source paper, not a newly invented repository entry.

### Sources

1. OpenProblemsInNLA. [IS-04: A condition number of two for a sign matrix in every dimension](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/eigenvalues-and-inverse-problems/IS-04/README.md). Statement and audit update of 10 September 2026. Accessed 11 September 2026.

2. Boris Alexeev, John Jasper, and Dustin G. Mixon. [*Asymptotically optimal approximate Hadamard matrices*](https://arxiv.org/html/2511.14653v1). arXiv:2511.14653v1, 18 November 2025. Section 6, Problems 12 and 13. The former is the all-order source question; the latter is the separate explicit odd-family question.

3. Étienne Fouvry, Emmanuel Kowalski, and Philippe Michel. [*Algebraic twists of modular forms and Hecke orbits*](https://arxiv.org/html/1207.0617v5). arXiv:1207.0617v5, 16 November 2014. Proposition 10.1, equation (8.8), and Section 9, including (9.4) and the subsequent weight argument. The weight input cited there is Deligne's *La conjecture de Weil, II*, Publ. Math. IHÉS 52 (1980), Theorem 3.3.1. Section 4 explains the specialization used here.

[^repo]: Source 1, the unrestricted all-dimensions statement.

[^ajm]: Source 2, Section 6, Problem 13.

[^weil]: Source 3: Proposition 10.1 supplies the mixed-character sheaf and ramification, (8.8) the Euler–Poincaré formula, and Section 9 the trace and weight estimate.
