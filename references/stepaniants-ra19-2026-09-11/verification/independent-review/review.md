# RA-19 — independent mathematical review

**Verdict: PASS for the complete canonical target, for every integer $n\ge3$.**

**Reviewer:** separate Codex agent `/root/prepare_manuscripts`, independently of the proof author `/root/review_aa01`. Completed 12 September 2026, 00:48 UTC (11 September in the user's local time zone). This is a mathematical agent review, not external human peer review, a Lean verification, or a formal proof certificate.

## Exact versions and scope

The reviewed manuscript is [RESULT.md](../RESULT.md), 19,069 bytes, SHA-256:

`475e29760333fc215e80eed33e4729649383d112d585d7cca88a8b669b618c22`.

I read and checked the whole frozen manuscript, including all three lemmas, every generic condition and its simultaneous witness, the exceptional dimension, and the stated scope. I made no manuscript edits. This verdict concerns the proof of

$$\operatorname{EDdeg}\{X\in\mathbb C^{n\times n}:\det X=0,\ x_{11}=0\}=5n-7\qquad(n\ge3),$$

for the bilinear squared Frobenius distance and generic complex data, with critical points taken on the smooth locus. It does not concern other zero patterns, counts for nongeneric data, or the reality of the critical points.

The [canonical target snapshot](../canonical-target.md) is 3,180 bytes, SHA-256 `82c6595ec538a86623a818ad650a53b6520dd9c93997f1a99726408a2c042bf4`. I checked that it agrees byte-for-byte with `randomized-and-low-rank-approximation/RA-19/README.md` at the available `upstream/main` commit `1f22006bdaa4659fcaa0bb775a887685cd3cc566`. This check preserves the original target and its explicit $n\ge3$ restriction; it is not a publication-eligibility audit.

## Primary source

I checked Kubjas, Sodomaco and Tsigaridas, [arXiv:2010.15636v2](https://arxiv.org/abs/2010.15636v2), including the [primary PDF](https://arxiv.org/pdf/2010.15636v2). The local PDF has SHA-256 `d1eab00e8975a5b36adaea8456bc105622114a8a917d59c73190accc861d673c`. I read the extracted text and individually inspected the rendered manuscript pages 4 and 19.

Section 2.2 on page 4 uses the complex bilinear extension of squared Euclidean distance and smooth-locus critical points. Conjecture 5.1 on page 19, for the single zero $S=\{(1,1)\}$ and corank one, gives $5(n-1)-2$. Table 2 begins at $n=3$ and reports the values stated by the canonical page. Thus the proof addresses the original formula, with the canonical page's disclosed dimension-two correction. The source's finite computations are not used to infer the all-dimension result. Attribution to the three original conjecture authors is accurate.

## Spectral reduction and critical-point correspondence

I independently reconstructed the block linearization that gives equations (1)–(3). Eliminating the lower coordinates of the symmetric matrix with off-diagonal blocks $A(z)$ and $A(z)^T$ produces the displayed $2\times2$ determinant. Multiplication by $f$ gives the monic characteristic polynomial. The putative double poles cancel, yielding the polynomial identity $fh+g^2=\lambda F_bF_c$. No factor depending on $z$ or $\lambda$ is omitted.

The generic complex orthogonal reduction of $D$ is valid. A simple eigenvector of a complex symmetric matrix is nonisotropic; distinct eigenvalues supply an orthogonal eigenbasis. Nonzero squared eigenvalues then supply the right orthogonal factor. The transformations act only on the last $m$ rows and columns, preserve $x_{11}=0$, and preserve the bilinear metric. Generic reducedness is invariant under these transformations. Since their translates of the diagonal family cover a dense open set of the full data space, working with diagonal $D$ does not force the proof into an exceptional data locus.

I checked the normal-space argument in both directions. The determinant restricted to $x_{11}=0$ is nonzero and squarefree because it is multiaffine in the remaining entries. At a smooth point the rank is exactly $n-1$, and the determinant gradient and $E_{11}$ are independent. The normal directions are therefore precisely $E_{11}$ and $uv^T$, where $u,v$ are left and right kernel vectors.

The exclusions needed to pass from normal equations to spectral coordinates are justified:

- A zero rank-one residual would force $A(0)$ singular, excluded by $z_*\ne0$ and invertible $D$.
- An isotropic kernel vector would put the completion at $z=z_*$ and contradict its prescribed nonisotropic left or right kernel.
- A repeated eigenvalue with a nonisotropic eigenvector splits off that eigenvector orthogonally. The complementary summand would contain another eigenvector for the same eigenvalue; the adjugate would vanish, forcing $P=P_\lambda=P_z=0$. This contradicts the smooth spectral curve established from squarefreeness of $\lambda F_bF_c$ and $g\ne0$ at the roots of $f$.
- The derivative identity $\lambda'=2(\Pi A)_{11}$ has the correct sign and normalization. Consequently $X_{11}=0$ is exactly $E=0$.

Conversely, a common zero of $P,E$ has $P_\lambda\ne0$, $\lambda\ne0$, and invertible $A(z)$. The adjugate projector is regular there. The matrix $X=(I-\Pi)A$ has rank $n-1$ and the correct fixed entry. If its determinant normal were proportional to $E_{11}$, both kernels would equal the first coordinate line and the first off-diagonal row of $A$ would vanish, contradicting $b\ne0$. Thus it lies on the smooth locus and is distance critical. The forward and reverse maps are inverse; no extra sign from a square root of $\lambda$ survives the projector construction.

## Independent universal algebra verification and degree

I wrote [universal_algebra_check.py](universal_algebra_check.py) independently, without reading, importing, or running the proof author's checker. It uses only standard-library integer arithmetic in the formal polynomial ring

$$\mathbb Z[f,g,h,f',g',h'].$$

It is not a finite-order numerical test. It checks all four coefficients of the universal identity

$$f^2E-(\alpha z+\beta)
=\bigl(ff'z+2fg'-2f'g\bigr)P,$$

and independently expands all 120 permutation terms of the $5\times5$ Sylvester determinant to verify

$$f^2\operatorname{Res}_z(P,E)
=h\alpha^2+2g\alpha\beta-f\beta^2.$$

Both identities passed exactly. The expanded resultant has 16 terms. The code binds its output to the frozen manuscript hash. The [output](universal-algebra-check.json) records the assertions and their scope. Code SHA-256: `67c52fe6b788cc5530301a7ccd2d55aa94355be7dbc7bd7e1b84062d23d6a769`. Output SHA-256: `79d7fca0557f407d3ba320a80b58c98ac402a5d424b75481f839ff87edff1b25`.

I separately checked the all-$m$ degree argument. Writing $h=\lambda f+r$, $\deg r\le m$, cancels the highest Wronskian term and gives $\deg\alpha\le3m-2$. With leading coefficient $G\ne0$ for $g$, the leading term of $\beta$ is $G\lambda^{3m-1}$. Hence $-f\beta^2$ is the unique numerator term of degree $7m-2$, with coefficient $-G^2$; the other terms cannot cancel it. Exact division by monic $f^2$ gives degree $5m-2$. The division follows from the original Sylvester identity, so it introduces no unsupported saturation argument.

At $f=0$, the homogeneous quadratic $P$ has a root at infinity in $z$, but the homogeneous cubic $E$ does not, because $f'\ne0$. Finite common roots there are separately excluded. For $f\ne0$, the quadratic leading coefficient stays nonzero and the ordinary resultant criterion applies. The proof correctly excludes $\lambda=0$ through $zP_\lambda$, rather than accidentally removing or retaining a spurious fixed factor.

## Simultaneous generic exclusions, for every dimension

I checked the real small-$\epsilon$ witness with $b=\epsilon\beta$, $c=r\epsilon\beta$, $\beta_i>0$, distinct positive $d_i$, and $r>0$, $r\ne1$.

The two positive rank-one secular perturbations have simple positive roots and disjoint spectra; no root lies at a pole. Their common-root equations would require $r^2=1$. The roots of $g/\epsilon^2$ strictly interlace the poles and remain separated from the limiting roots of $h$, proving the stated coprimality. The conditions at zero and at the poles are nonvanishing as claimed.

At $\lambda=d_i^2$, the unique finite $z$ root tends to $-(1+r^2)d_i/(2r)$, whose absolute value exceeds $d_i$. Substitution into $E$ gives the stated nonzero limit. Thus no common point remains over a root of $f$.

At the singular completion, $A(z_*)$ has rank $m$ and real nonisotropic kernels. Its zero squared singular value is simple and has $E=z_*P_\lambda\ne0$. I independently expanded the simple nonzero eigenvectors: the first left component is $\epsilon\beta_i/d_i+O(\epsilon^3)$ and the first component of $A^Tu_i$ is $r\epsilon\beta_i+O(\epsilon^3)$. This gives

$$\bigl(A(z_*)-\Pi_iA(z_*)\bigr)_{11}
=r\epsilon^2\sum_{j\ne i}\frac{\beta_j^2}{d_j}+O(\epsilon^4).$$

The leading coefficient is strictly positive precisely because $m\ge2$. There are finitely many indices and conditions for each fixed dimension, so one sufficiently small positive $\epsilon$ satisfies all of them simultaneously. Their failure sets are algebraic, yielding a nonempty complex algebraic open set for each $m\ge2$. This is an all-dimension witness, not extrapolation from finitely many examples.

## Reducedness and exact counting

Lemma 3 is needed: a set-theoretic correspondence alone would not identify resultant degree with the number of distinct critical points. I checked the additional local-structure argument.

The translated normal bundle over the smooth locus is smooth of dimension $n^2$. The nonzero resultant and the bijection make its generic data fibers finite. Dominating components are generically separable in characteristic zero; after deleting a proper algebraic exceptional set, their fibers are reduced. The closures of nondominating images can also be deleted.

On the good open set, the ordinary corank-one critical correspondence is locally isomorphic to the simple spectral cover. Its forward coordinate can be written explicitly as

$$\lambda=\operatorname{tr}\bigl((A-X)(A-X)^T\bigr),$$

and its inverse is the regular adjugate-projector formula. Restricting $X_{11}=0$ is transverse precisely when $X$ is smooth on the constrained variety: the ordinary correspondence is a vector bundle over rank-$n-1$ matrices, and the determinant normal is independent of $E_{11}$. In spectral coordinates the same constraint is exactly $E/P_\lambda$, not merely an equation with the same zero set. The extra data coordinate $u_{11}$ is a free affine factor. This establishes the local scheme equivalence needed to transfer generic reducedness to $P=E=0$.

At any common point, $z\ne0$ by $\gcd(g,h)=1$. Hence $P_z=-2zP_\lambda\ne0$. The two quadratic roots are locally distinct analytic branches in $\lambda$, and the resultant is a nonzero local factor times the product of $E$ evaluated on those branches. Its multiplicity is the sum of the local intersection multiplicities, which are one at a generic reduced fiber. Distinct pairs sharing a value of $\lambda$ are counted with the appropriate summed multiplicity. Consequently the univariate degree counts exactly the distinct smooth-locus critical points.

The $n=2$ exception is correctly diagnosed. At the singular completion, deleting the sole nonzero singular component gives the singular point $X=0$ of the two-component variety. The sum excluding this artifact is empty when $m=1$. The draft does not apply its formula to that excluded dimension.

## Conclusion and limits of verification

I found no mathematical gap in the frozen proof. The complete canonical claim follows for every $n\ge3$. No mathematical correction is required before a faithful publication conversion. The clarifications above about the regular inverse spectral coordinate and invariance of the generic reducedness locus make explicit steps already justified by the manuscript; they do not add a new hypothesis or change its substance.

This review combines an independent mathematical reconstruction with exact universal algebra checks. It is not a machine-checked proof of algebraic geometry, an external human review, or verification of every numerical datum in the source paper. I have not approved later converted Markdown, TeX, PDFs, or changed source versions; those require a separate preservation audit. Current public status and submission eligibility remain the publishing agent's responsibility.

**Signed:** `/root/prepare_manuscripts` — independent Codex review, exact frozen version identified above.
