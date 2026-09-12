# SP-13: trace-norm-small perturbations of Hermitian sequences

**Status:** complete proof candidate, pending independent mathematical review. No public status, repository artifact, or submission has been changed. The argument uses a published, dimension-independent weak-type theorem for triangular truncation; that external theorem is explicitly identified below.

## 1. Exact target

For $A_n\in\mathbb C^{n\times n}$ and measurable $f:[0,1]\to\mathbb R$, the notation $\{A_n\}\sim_\lambda f$ means

$$\lim_{n\to\infty}\frac1n\sum_{j=1}^n F(\lambda_j(A_n))
=\int_0^1 F(f(t))\,dt\qquad(F\in C_c(\mathbb C)).$$

The functions are continuous, complex-valued, and compactly supported. Eigenvalues have algebraic multiplicity. The trace norm is $\|X\|_* = \sum_j\sigma_j(X)$; $X^*$ is the conjugate transpose.

**Theorem.** Suppose $H_n=H_n^*$, $\{H_n\}\sim_\lambda f$, and $E_n\in\mathbb C^{n\times n}$ satisfies $\|E_n\|_*/n\to0$. Then

$$\{H_n+E_n\}\sim_\lambda f.$$

There is no spectral-norm boundedness assumption on either sequence and no normality assumption on $H_n+E_n$. This is the complete canonical SP-13 target and Conjecture 1 in Section 6, printed page 29, of Barbarino–Serra-Capizzano [BSC20].

## 2. The external weak-type theorem

For a finite matrix $X$ and $s>0$, set

$$n_X(s)=\#\{j:\sigma_j(X)>s\},\qquad
\|X\|_{1,\infty}=\sup_{s>0}s\,n_X(s).$$

Let $\mathcal T_+(X)$ retain the strictly upper-triangular entries of $X$ and replace all other entries by zero.

**Published weak-type estimate.** There is an absolute constant $C$ such that, for every matrix size and every complex matrix $X$,

$$n_{\mathcal T_+(X)}(s)\le \frac{C\|X\|_*}{s}\qquad(s>0).\tag{1}$$

This is the finite-matrix specialization of Randrianantoanina [R02, Theorem 4.8, printed page 23]. The source defines the weak-$L^1$ quasi-norm on printed page 12 by the distribution function used above. Its theorem applies to an arbitrary finite family of mutually orthogonal projections and has an **absolute** constant. Take the algebra $M_n(\mathbb C)$ with its ordinary, unnormalized matrix trace, and its rank-one coordinate projections. The source uses strictly lower-triangular truncation; reversing the order of the projections gives $\mathcal T_+$. Thus (1) is uniform in $n$ and imposes neither positivity nor self-adjointness on $X$.

Theorem 4.8 is explicitly attributed there to Dodds–Dodds–de Pagter–Sukochev [DDPS99, Theorem 1.4], and [R02] also supplies a proof from its noncommutative Hilbert-transform estimate. We use this published result; we do not claim it as a new theorem or replace it by the weaker logarithmic trace-norm bound.

## 3. Two elementary spectral facts

For arbitrary matrices $X,Y$ and $a,b>0$,

$$n_{X+Y}(a+b)\le n_X(a)+n_Y(b).\tag{2}$$

Indeed, remove the singular components of $X$ larger than $a$, and of $Y$ larger than $b$. The remaining sum has spectral norm at most $a+b$, while the removed sum has rank at most the right side. The min-max characterization of singular values proves (2). Also

$$n_X(a)\le\frac{\|X\|_*}{a}.\tag{3}$$

**Lemma.** Let $A_n,B_n$ be Hermitian matrices of size $n$. If

$$\frac{n_{A_n-B_n}(s)}n\longrightarrow0\qquad\text{for every fixed }s>0,\tag{4}$$

then for every $g\in C_c(\mathbb R)$,

$$\frac1n\operatorname{tr}g(A_n)-\frac1n\operatorname{tr}g(B_n)\longrightarrow0.\tag{5}$$

No bound on $\|A_n\|$ or $\|B_n\|$ is required.

**Proof.** Fix $s>0$. Split the Hermitian matrix $A_n-B_n$ by its spectral decomposition into $R_n+S_n$, where $R_n$ contains the eigenvalues with absolute value greater than $s$. Then

$$\operatorname{rank}R_n=n_{A_n-B_n}(s)=o(n),\qquad\|S_n\|\le s.$$

For Hermitian matrices differing by rank at most $r$, their eigenvalue counting functions differ by at most $r$ at every real threshold. This follows from the min-max principle by restricting a trial subspace to the kernel of the rank-$r$ difference. Consequently, for $g\in C_c^1(\mathbb R)$, integration by parts against the finite eigenvalue counting measures gives

$$\left|\operatorname{tr}g(A_n)-\operatorname{tr}g(B_n+S_n)\right|
\le \operatorname{rank}R_n\int_{\mathbb R}|g'(x)|\,dx.\tag{6}$$

The eigenvalues of $B_n+S_n$ and $B_n$, arranged in increasing order, differ by at most $s$, again by min-max. With

$$\omega_g(s)=\sup_{|x-y|\le s}|g(x)-g(y)|,$$

their normalized trace difference is at most $\omega_g(s)$. Thus the limsup of the absolute value in (5) is at most $\omega_g(s)$. Compactly supported continuous functions are uniformly continuous, so letting $s\downarrow0$ proves (5) for $g\in C_c^1(\mathbb R)$. Every $g\in C_c(\mathbb R)$ can be uniformly approximated by such functions; each normalized trace changes by at most the uniform error. This proves the lemma, also for complex-valued $g$. $\square$

## 4. Schur decomposition and the finite-dimensional estimates

Fix $n$, write $H=H_n$, $E=E_n$, and let $q=\|E\|_*$. Take any unitary Schur decomposition

$$U^*(H+E)U=T=D+iJ+N,$$

where $D$ and $J$ are real diagonal matrices and $N$ is strictly upper triangular. The diagonal entries of $D+iJ$ are exactly the eigenvalues of $H+E$, counted with algebraic multiplicity. Set

$$G=U^*HU,\qquad Z=U^*EU,\qquad
K=\operatorname{Im}T=\frac{T-T^*}{2i}.$$

Because $G$ is Hermitian,

$$K=\operatorname{Im}Z,\qquad \|K\|_*\le\|Z\|_*=q.\tag{7}$$

For a strictly upper-triangular entry, $K_{ij}=N_{ij}/(2i)$. Therefore

$$N=2i\,\mathcal T_+(K).$$

The dimension-independent estimate (1) yields

$$n_N(s)\le\frac{2Cq}{s}.\tag{8}$$

Applying (2) to $(N+N^*)/2$ gives

$$n_{\operatorname{Re}N}(s)\le2n_N(s)\le\frac{4Cq}{s}.\tag{9}$$

Taking Hermitian parts in $G+Z=D+iJ+N$ gives

$$D-G=\operatorname{Re}Z-\operatorname{Re}N.$$

Since $\|\operatorname{Re}Z\|_*\le q$, equations (2), (3), and (9) show, for every $s>0$,

$$n_{D-G}(s)
\le n_{\operatorname{Re}Z}(s/2)+n_{\operatorname{Re}N}(s/2)
\le\frac{(2+8C)q}{s}.\tag{10}$$

Finally, the diagonal of $K$ is $J$, and

$$\sum_{j=1}^n|J_{jj}|\le\|K\|_*\le q.\tag{11}$$

For clarity, the first inequality needs no bound on a triangular projection: if $S$ is the diagonal matrix with entries $\operatorname{sgn}(K_{jj})$, then $\|S\|\le1$ and $\sum_j|K_{jj}|=\operatorname{tr}(SK)\le\|K\|_*$. Equivalently it is trace-norm contractivity of diagonal pinching.

All estimates (7)–(11) hold for every finite $n$, independently of $H$, the Schur ordering, diagonalizability, or the spectral norm of $E$.

## 5. Passage to the prescribed test functions

Return to the sequences, so $q_n/n\to0$. By (10), for every fixed $s>0$,

$$\frac{n_{D_n-U_n^*H_nU_n}(s)}n\longrightarrow0.$$

The lemma implies that $D_n$ and $H_n$ have asymptotically equal normalized traces for all $g\in C_c(\mathbb R)$. In particular, for a prescribed $F\in C_c(\mathbb C)$, the restriction $g(x)=F(x)$ to the real axis belongs to $C_c(\mathbb R)$, and

$$\frac1n\sum_jF((D_n)_{jj})-\frac1n\sum_jF(\lambda_j(H_n))\longrightarrow0.\tag{12}$$

Write $d_{nj}=(D_n)_{jj}$ and $y_{nj}=(J_n)_{jj}$. Equation (11) implies

$$\#\{j:|y_{nj}|>s\}\le\frac{q_n}{s}.$$

Every continuous compactly supported function on $\mathbb C$ is uniformly continuous on the whole plane. Defining its modulus $\omega_F(s)$ using Euclidean distance in $\mathbb C$, we obtain

$$\begin{aligned}
&\left|\frac1n\sum_jF(d_{nj}+iy_{nj})-\frac1n\sum_jF(d_{nj})\right|\\
&\hspace{2em}\le\omega_F(s)+2\|F\|_\infty\frac{q_n}{ns}.
\end{aligned}\tag{13}$$

For every fixed $s>0$ the second term tends to zero. Then $s\downarrow0$ makes the first term tend to zero. The values $d_{nj}+iy_{nj}$ are the eigenvalues of $H_n+E_n$ with their algebraic multiplicities. Combining (12), (13), and the assumed spectral distribution of $H_n$ proves

$$\lim_{n\to\infty}\frac1n\sum_jF(\lambda_j(H_n+E_n))
=\int_0^1F(f(t))\,dt.$$

This holds for every $F\in C_c(\mathbb C)$ and is exactly the asserted conclusion. $\square$

## 6. Scope, provenance, and bounded source check

The proof allows arbitrary complex perturbations and arbitrary real measurable symbols on the canonical domain. Its only smallness assumption is $q_n/n\to0$. Large exceptional singular values and eigenvalues are handled by rank bounds and compactly supported test functions, so no uniform spectral bound enters implicitly.

The substantive connection is the application of the published weak-type triangular-truncation theorem to the imaginary Hermitian part of a Schur form. The external theorem and the original conjecture retain their original authorship. This private proof candidate was developed with substantial Codex assistance and is awaiting a separate agent's adversarial review; no human peer-review or formal-verification claim is made.

A read-only public-network check completed at 2026-09-12 00:53:36 UTC examined five public repositories, all 37 returned branch heads, 98 distinct selected text blobs, and 32 PR review bodies. SP-13 pages were either Partially resolved or absent on pre-admission branches. The matching discussions were the admission PR 111 and unrelated trace-norm references concerning MI-25; no prior full SP-13 resolution was located. The snapshot and portable checker are saved alongside this note. Private, deleted, unpublished, or unidentifiably named work is outside this bounded check.

The primary 2020 source states the conjecture without spectral bounds in Section 6. The current arXiv record for Barbarino's related 2018 note remains v1. The 2025 Barbarino–Garoni normal-sequence paper was checked as context; its additional conditions are not premises of this proof.

## References

- **[BSC20]** G. Barbarino and S. Serra-Capizzano, *Non-Hermitian perturbations of Hermitian matrix-sequences and applications to the spectral analysis of the numerical approximation of partial differential equations*, Numerical Linear Algebra with Applications 27 (2020), e2286. [DOI](https://doi.org/10.1002/nla.2286), [author PDF](https://giovannibarbarino.github.io/doc/articles/NHperturbation.pdf). Conjecture 1, Section 6, printed page 29; the spectral-distribution convention appears on printed page 2.
- **[R02]** N. Randrianantoanina, *Spectral subspaces and non-commutative Hilbert transforms*, Colloquium Mathematicum 91 (2002), 9–27. [DOI](https://doi.org/10.4064/cm91-1-2), [publisher PDF](https://www.impan.pl/shop/en/publication/transaction/download/product/87479). Theorem 4.8, printed page 23, and its proof on page 24; weak-$L^1$ definition on printed page 12.
- **[DDPS99]** P. G. Dodds, T. K. Dodds, B. de Pagter and F. A. Sukochev, *Lipschitz continuity of the absolute value in preduals of semifinite factors*, Integral Equations and Operator Theory 34 (1999), 28–44. Theorem 1.4 is the result cited by [R02, Theorem 4.8]; the application above uses the statement and proof actually checked in [R02].
- **[B18]** G. Barbarino, *Conjectures on Perturbations of Hermitian Sequences*, [arXiv:1808.05555v1](https://arxiv.org/abs/1808.05555v1), 2018. Context for equivalent formulations, not an additional assumption.
- **[BG25]** G. Barbarino and C. Garoni, *GLT sequences and normal matrices*, Electronic Journal of Linear Algebra 41 (2025), 1–20. [Primary PDF](https://journals.uwyo.edu/index.php/ela/article/download/8929/6949/23285). Theorem 3.2, contextual comparison only.
