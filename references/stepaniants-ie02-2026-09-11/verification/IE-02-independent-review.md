# Independent review of the complete IE-02 proof

**Verdict: PASS for the full canonical complex target.** No mathematical gap or additional hypothesis was found. This is an independent AI-agent mathematical review, not human peer review, a novelty certification, or formal proof-assistant verification.

Reviewer: `/root/review_md03_md04`, which did not author the IE-02 argument. Review completed 11 September 2026. The review reads and evaluates the complete proof, independently reconstructs its reasoning, and checks the exact external theorem against its primary publisher PDF. No numerical experiment is used as evidence of universal validity.

## Exact reviewed version

Source: `/tmp/nla-fresh-round2/ie02/RESULT.md`.

- Size: **11759 bytes**.
- SHA-256: **64bbb398344d56651a1a59c65613817bc932cea6772483893a5fc195ce3d9fb9**.

The reviewer did not modify that file. The canonical target was separately read from `/tmp/nla-mf22-worktree/linear-systems-and-elimination/IE-02/README.md`.

The target quantifies over every $n\ge2$, every nonzero complex $\lambda$, every $1\le k<n$, complex unit vectors, and complex polynomials of degree at most $k$ with $p(0)=1$. The source's Theorem 1 states exactly this equality. The proof establishes it without a simplicity assumption on the top singular value, without a condition that $k$ divide $n$, and without any restriction on the phase or magnitude of $\lambda$.

## 1. Primary source: the finite Carathéodory–Fejér theorem

I directly opened and read the primary publisher PDF of Courtney and Sarason, *A mini-max problem for self-adjoint Toeplitz matrices*, Mathematica Scandinavica **110** (2012), 82–98:

[Publisher PDF](https://www.mscand.dk/article/download/15198/13193/34699), **Theorem CF, Section 2, printed page 84**, together with the definitions on page 82; [DOI](https://doi.org/10.7146/math.scand.a-15198).

Despite the paper's title, this theorem explicitly concerns the **lower triangular** case of the general complex Toeplitz matrix introduced in Section 1. Its minimizing multiplier has norm equal to the finite matrix's operator norm and is a finite Blaschke product of order at most $N$ multiplied by that norm. The matrix size is $N+1$ and the compression space consists of polynomials of degree at most $N$. Taking $N=n-1$ gives precisely the existence assertion used by the manuscript. The theorem is not restricted to self-adjoint matrices, real coefficients, a nonzero diagonal entry, or a simple maximal singular value.

Only this existence/compression consequence is required; uniqueness is not used. A nonzero matrix has positive norm, so division by $t$ is valid. The source manuscript separately treats the zero residual matrix and allows constant Blaschke products.

## 2. Maximal singular subspace: independently reconstructed

Let $t=\|T\|_2>0$ and let the finite inner multiplier be $B=a/b$, with $a,b$ as in equations (3)–(4). Every zero of $a$ lies inside the open disk; every zero of a nonconstant factor of $b$ lies outside the closed disk. Thus $a$ and $b$ are relatively prime, $\deg a=d$, $\deg b\le d$, and neither division nor the boundary identities introduce a pole on the unit circle. Zero Blaschke roots merely lower the degree of $b$ and cause no exception.

Since multiplication by $B$ preserves the circle $L^2$ norm and $T=t\Pi_n M_B$ on $\mathcal H_n$, equality $\|Tf\|=t\|f\|$ holds exactly when $Bf\in\mathcal H_n$. This is also exactly the maximal right singular subspace, because $t^2I-T^*T$ is positive semidefinite.

If $Bf=g\in\mathcal H_n$, then $af=bg$. Coprimality forces $f=bh$ and $g=ah$. The condition on $g$ forces $\deg h\le n-1-d$; conversely that bound ensures **both** $bh$ and $ah$ belong to $\mathcal H_n$, even when $\deg b<d$. Hence equations (5)–(6) are exact descriptions of the entire maximal singular subspace, including multiplicity greater than one. This is the structural step needed later; it is not a selection of one specially convenient singular vector.

## 3. Scalar spectral factorization and preservation of all moments

The algebraic proof of Lemma 3 is sound. For a nonzero, nonconstant nonnegative trigonometric polynomial $Q$ with effective degree $\ell$, the polynomial $z^\ell Q(z)$ has degree $2\ell$ and nonzero constant term. Conjugate-reciprocal symmetry pairs its off-circle roots, with the same multiplicities. Nonnegativity of the real analytic boundary function gives even multiplicity to each circle root. Selecting one root from each off-circle pair and half of each circle multiplicity constructs a degree-$\ell$ polynomial $h_0$.

More explicitly, the product of $h_0$ with its reversed conjugate has exactly the roots and multiplicities of $z^\ell Q(z)$. The two polynomials therefore differ by a constant. On the unit circle, cancellation of $z^\ell$ gives $Q=\beta|h_0|^2$. Evaluating at a point where $Q>0$ makes $\beta$ positive real, justifying the final scaling. The zero and constant cases are covered separately. Thus the resulting factor has degree at most the stated $m$, without requiring a vector-valued factor or a larger degree.

For Lemma 4, writing every unit maximizing vector as $f_\nu=bh_\nu$ and factoring the positive combination $\sum\omega_\nu|h_\nu|^2$ therefore gives a **single** polynomial $h$ in the same permitted degree range. The choice $f=bh$ remains in the maximal singular subspace. Its norm is one by integrating the preserved modulus against $|b|^2$.

The decisive complex moment identity was checked directly using the manuscript's convention that the inner product is linear in its second argument:

$$
\langle Tf,R_jf\rangle
=t\langle ah,\Pi_n(r_jbh)\rangle
=t\int_{\mathbb T}\overline a\,r_jb\,|h|^2.
$$

The projection is removed because **$ah\in\mathcal H_n$**; no assertion that $r_jbh$ has degree below $n$ is needed. The factor $t$ is positive real. Pointwise preservation of $|h|^2$ preserves this complex integral simultaneously for every symbol $r_j$. Both real and imaginary parts are therefore preserved, and equation (8) is stronger than merely preserving real directional derivatives.

## 4. Optimality with a multiple maximal singular value

Lemma 5 is valid for a complex affine matrix space. The set of moment vectors is compact because the unit sphere of the finite-dimensional maximal singular subspace is compact. Its convex hull is compact in $\mathbb R^{2k}$. If zero is outside, strict real separation is available.

Every real linear functional on $\mathbb C^k$ can be written as $\operatorname{Re}\sum c_jz_j$, so the separating direction is indeed $D=\sum c_jR_j$ with complex coefficients. No missing conjugation obstructs the choice of coefficients. Separation makes $\operatorname{Re}\langle Tf,Df\rangle$ uniformly positive on all unit maximizing vectors. Continuity makes it uniformly positive on a neighborhood in the full sphere. On the compact complement there is a strict uniform gap below $t^2$ in $\|Tf\|^2$, since all norm-attaining vectors are in that neighborhood.

For sufficiently small positive real $\varepsilon$, the exact squared-norm expansion for $T-\varepsilon D$ strictly lowers the maximum on both regions: the linear negative term controls the neighborhood, and the old spectral gap controls its complement. If the complement is empty, only the first estimate is needed. This contradicts minimality. Thus zero lies in the convex hull, and a finite convex combination supplies (11). Linear dependence of the $R_j$ is harmless.

This argument does not differentiate a possibly nonsmooth largest singular value or assume that its eigenspace is one-dimensional.

## 5. Affine minimax conclusion and attainment

The minimum in the finite-dimensional affine matrix space is attained: intersecting a minimizing sequence with a sufficiently large closed norm ball gives a compact set. If the minimizer is zero, both sides of the proposed minimax equality vanish.

For a nonzero minimizer $T=Y-X_*$, Lemma 5 supplies a convex combination of maximal-singular-vector moments that vanish in every direction. Lemma 4 turns that combination into one unit vector $f$ that still satisfies $\|Tf\|=t$ and all complex orthogonality conditions. For every $X$ in the complex span,

$$
\|(Y-X)f\|^2
= t^2+\|(X_*-X)f\|^2\ge t^2.
$$

Taking $X=X_*$ attains equality. The opposite bound follows from the operator norm, and the constructed $f$ proves that the outer maximum is attained; no continuity assertion about a changing least-squares rank is required. For each fixed $f$, the image of the finite-dimensional span under $X\mapsto Xf$ is a closed subspace, so the inner least-squares minimum is also legitimate. The stronger triangular Toeplitz affine statement is therefore proved in full.

## 6. Exact reduction to the canonical Jordan-block problem

The unitary reversal matrix sends the superdiagonal shift to the lower shift and leaves the scalar $\lambda I$ unchanged. Hence $A=WJ_n(\lambda)W^*=\lambda I+S$ is lower triangular Toeplitz, as are its powers. With $Y=I$ and $\mathcal X=\operatorname{span}_{\mathbb C}\{A,\ldots,A^k\}$, the residual matrices $Y-X$ are exactly $p(A)$ with $p(0)=1$ and $\deg p\le k$. The sign in $Y-X$ is immaterial because all polynomial coefficients in the span are free.

Unitary conjugation preserves operator norms, Euclidean vector norms, and the bijection of unit vectors used in the outer maximum. This proves the precise equality requested for all allowed complex $\lambda$ and every $1\le k<n$. It does not replace the input by a doubled matrix or assume a real-vector interpretation when the canonical problem permits complex vectors.

The manuscript's separate positivity observation is also correct: a polynomial of degree less than $n$ cannot annihilate a size-$n$ Jordan block unless it is identically zero, contradicting $p(0)=1$. The main proof does not need this extra observation, since the general affine theorem already handles a zero minimum.

## 7. Source and claim boundaries

I separately opened the primary [Tichý–Liesen–Faber author manuscript](https://www.karlin.mff.cuni.cz/~ptichy/download/public/TiLiFa2007.pdf), especially its introductory Jordan-block conjecture and the discussion of multiple maximal singular vectors, and the [Faber–Liesen–Tichý approximation paper](https://arxiv.org/html/2506.09687). The new argument does not silently import their partial cases as a full result. The only external theorem necessary to the proof is the clearly attributed finite Carathéodory–Fejér theorem; the scalar factorization and convex optimality arguments are supplied explicitly.

This review does not certify exhaustive literature novelty, all public branches/forks, PDF rendering, contribution-format compliance, or permission to publish. Those are separate tasks. No numerical optimizer, rounding assumption, unproved spectral positivity pattern, or generic-singular-value hypothesis enters the reviewed proof.

**Final mathematical verdict: PASS. The reviewed version proves the complete canonical IE-02 statement. No correction is required before mathematical acceptance.**
