# RA-13 — exact mathematical and numerical specification

## Review and implementation state

This is a **preimplementation specification draft**, authored by OpenAI Codex AI agent `/root/statement_design` on
2026-09-28. Two independent statement reviews remain required. No Lean declaration
or proof is implemented by this draft. The canonical status remains **Solved**
on the previously recorded evidence; this file makes no new verification claim.

The complete canonical target copied below governs this specification. Its raw
file hash preserves the resolution and historical notes as well. Supporting
lemmas or stronger results must not replace the original target. Historical
manuscripts may quote hashes of earlier submission bodies; those are different
objects from the raw-byte source hashes recorded here.

An uninterpreted probability, norm or algorithm oracle, an assumed answer, or a
predicate defined to mean the desired conclusion is not a formalization. All
actual definitions must be independently reviewed. A statement is not a proof.

## Frozen canonical identity

- Permanent ID: `RA-13`.
- Canonical README: `randomized-and-low-rank-approximation/RA-13/README.md`.
- Frozen repository revision: `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`.
- Source status at that revision: `Solved`.
- Existing-statement check: no `.lean` files under `randomized-and-low-rank-approximation/RA-13/`.

| Source file | Raw-byte SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-13/README.md` | `16a973ffc9040332e2a521a6a2d2938dcb95df736304185f88ea195a8c78a377` |
| `randomized-and-low-rank-approximation/RA-13/problem.tex` | `fcbe9de6b7c19a9a3729b26ca834fd27adbaaabcf52c7242c829c117902c0386` |
| `randomized-and-low-rank-approximation/RA-13/solution.md` | `afc1b17cc61164093c5038e786934bc710ef141b9747c9a8a10ca8ab16414677` |
| `randomized-and-low-rank-approximation/RA-13/solution.tex` | `8bfde617822abef81989b3c1da94f9390f0e56cad23efaa37f107f91f42e63f9` |

## Exact target and quantifier order

For every \(n\ge1\), **nonzero real symmetric** \(A\) (possibly indefinite or
zero trace), and integer \(m\ge1\), define
\[
\lambda=\|A\|_2,\quad\phi=\|A\|_F,\quad\rho=\phi^2/\lambda^2,\qquad
B_{\lambda,\phi}=\lambda\operatorname{diag}
(I_{\lfloor\rho\rfloor},\sqrt{\rho-\lfloor\rho\rfloor}),
\]
and \(X\sim\operatorname{Gamma}(m\rho/2,m/(2\lambda))\) in shape/rate convention.
For every real
\[
\varepsilon\ge\frac{2\lambda}{m}
+\sqrt{\frac{2\phi^2}{m}+\left(\frac{2\lambda}{m}\right)^2},
\]
the complete target consists of both comparisons
\[
\Pr(|T_m(A)-\operatorname{tr}A|\ge\varepsilon)
\le2\Pr(T_m(B_{\lambda,\phi})-\operatorname{tr}B_{\lambda,\phi}\ge\varepsilon)
\]
and
\[
2\Pr(T_m(B_{\lambda,\phi})-\operatorname{tr}B_{\lambda,\phi}\ge\varepsilon)
\le2\Pr(X-\phi^2/\lambda\ge\varepsilon).
\]
Both must be named or conjoined, with identical data. The left event is
two-sided, the middle and final events are **upper tails**, with exact factor
2 on both. This is absolute error; no division by trace or absolute trace is
permitted.

## Concrete probability, norm and extremizer definitions

For any real symmetric \(d\times d\) matrix \(D\), use the product law of
\(m d\) independent standard real Gaussian coordinates. With row vectors \(z_j\),
\[
T_m(D)(z)=m^{-1}\sum_{j=1}^m z_j^TDz_j.
\]
Each probability is the measure of its event under that specific joint law,
in its own dimension. No coupling is needed. A random-variable formulation
must require the joint iid law, not only marginal laws. All events use
non-strict comparisons.

Spectral norm is Euclidean induced operator norm; Frobenius norm is
\(\phi=\sqrt{\sum_{ij}A_{ij}^2}\); trace is \(\sum_iA_{ii}\). Symmetry and
\(A\ne0\) imply \(\lambda>0,\phi>0,1\le\rho\le n\); these are derived facts.
Eigenvalues may have either sign. Let \(r=\lfloor\rho\rfloor\in\mathbb N\),
\(d_B=r+1\). The first \(r\) diagonal entries of \(B\) are \(\lambda\), the
last is \(\lambda\sqrt{\rho-r}\), and all off-diagonal entries zero.
Square root means the nonnegative real square root; \(0\le\rho-r<1\).
Keep a zero last entry at integer \(\rho\); \(B\)'s dimension need not be \(n\).

Gamma shape is \(\alpha=m\rho/2>0\) and **rate**
\(\beta=m/(2\lambda)>0\), with probability density
\[
g_{\alpha,\beta}(x)=
\begin{cases}\beta^\alpha x^{\alpha-1}e^{-\beta x}/\Gamma(\alpha)&x>0,\\0&x\le0.\end{cases}
\]
Its mean is \(\alpha/\beta=\phi^2/\lambda\). A scale/rate swap changes the
target. A concrete Gamma measure must replace any unspecified distribution
oracle. Exact probabilities can use nonnegative extended reals or justified
conversion to reals. A term \(2\Pr(\cdot)\) may exceed one; do not silently cap it.

## Endpoints and complete source correspondence

Include \(m=1,n=1\), indefinite and zero-trace matrices, repeated/zero
eigenvalues, integer/noninteger \(\rho\), and threshold equality. No PSD or
nonzero-trace condition is allowed. The canonical README explicitly resolves
a source prose inconsistency in favor of the **displayed threshold**, which
tends to zero for fixed \(A\) as \(m\to\infty\); it must not be replaced by a
formula tending to \(\phi\).

The archived Stepaniants solution, Sections 1 and 8, gives the exact bridge:
\[
\alpha=m/2,\quad w_i=\lambda_i(A)/\lambda,\quad
r=\rho=\sum_iw_i^2,\quad v=\alpha r,\qquad
Z_w=\sum_iw_i(G_i-\alpha),\quad G_i\text{ iid }\Gamma(\alpha,1).
\]
Then \(T_m(A)-\operatorname{tr}A\) has the law of \((2\lambda/m)Z_w\), and
\[
h=\frac{m\varepsilon}{2\lambda}\ge1+\sqrt{v+1}.
\]
The extremizer weights are \(\lfloor r\rfloor\) ones and
\(\sqrt{r-\lfloor r\rfloor}\), plus optional zeros. Its upper tail dominates
\(Z_w\)'s, and is dominated by \(J-v\) for \(J\sim\Gamma(v,1)\).
Applying the same bound to \(-w\) and adding tails yields factor 2.
Scaling gives the exact canonical Gamma shape, rate and mean. These Gaussian,
Gamma and scaling bridges must be proved if the normalized theorem is used;
that theorem alone is not the complete matrix statement.

Original source: Hallman, *Extremal bounds for Gaussian trace estimation*,
§5, Theorem 7 and Conjecture 4; [pinned v1](https://arxiv.org/html/2411.15454v1)
inspected 2026-09-28. Resolution: George Stepaniants, Department of Computing
and Mathematical Sciences, California Institute of Technology.
Colbrook's auxiliary inflection counterexamples retain their separate credit.

## Preimplementation review obligations

Inspect the concrete joint law, signed matrix domain, both upper-tail terms,
factors 2, Gamma rate, floor/square-root construction, threshold and absolute
centering. This target is mathematically specified; an inflection or bell-shape
assertion cannot replace the complete chain. Computation reduction may use
normalization but must preserve indefinite and zero-trace cases.

## Numerical work and verification boundary

No interval computation is required to state the problem. Retain exact constants,
all quantified inputs and every endpoint. A later certificate must use the shared
pinned LeanCert dependency, `set_option leancert.trust "kernel"`, explicit
`leancert (trust := kernel)` and `#assert_trust kernel` for exported results.
Symbolic statements need no artificial numerical calculation. Finite sample checks
or floating-point experiments cannot replace universal claims.

The eventual Lean boundary needs a type check and fresh review of all definitions.
Comparator statement identity is a separate mechanical gate; it cannot establish
fidelity to this prose. Challenge placeholders must never enter a purported proved
Solution. No build or placeholder identity comparison promotes the canonical status.

## Verbatim canonical target

The following target portion is copied exactly from the canonical README. The
full source hash above also preserves its resolutions and historical context.

<!-- canonical-target-start -->
## Problem statement

For a real symmetric $`d\times d`$ matrix $`D`$, define

```math
T_m(D)=\frac1m\sum_{j=1}^{m}z_j^TDz_j,
\qquad z_1,\ldots,z_m\overset{\mathrm{iid}}{\sim}N(0,I_d).
```

Let $`A\ne0`$ be an arbitrary real symmetric $`n\times n`$ matrix, possibly indefinite. Put

```math
\lambda=\|A\|_2,\qquad
\phi=\|A\|_F,\qquad
\rho=\frac{\phi^2}{\lambda^2},\qquad
B_{\lambda,\phi}
=\lambda\mathop{\mathrm{diag}}\nolimits\left(
I_{\lfloor\rho\rfloor},\sqrt{\rho-\lfloor\rho\rfloor}
\right).
```

The norms are the spectral and Frobenius norms. Let $`X`$ have Gamma shape $`m\rho/2`$ and rate $`m/(2\lambda)`$, so that $`\mathbb E X=\phi^2/\lambda`$. Here a Gamma variable with shape $`\alpha`$ and rate $`\beta`$ has density $`\beta^\alpha x^{\alpha-1}e^{-\beta x}/\Gamma(\alpha)`$ for $`x>0`$.

**Conjecture.** For every integer $`n\ge1`$, every such $`A`$, every integer $`m\ge1`$, and every  

```math
\varepsilon\ge
\frac{2\lambda}{m}
+\sqrt{\frac{2\phi^2}{m}
+\left(\frac{2\lambda}{m}\right)^2},
```

the following comparisons hold:

```math
\begin{aligned}
\Pr\!\left(|T_m(A)-\mathop{\mathrm{tr}}\nolimits(A)|\ge\varepsilon\right)
&\le
2\Pr\!\left(T_m(B_{\lambda,\phi})
-\mathop{\mathrm{tr}}\nolimits(B_{\lambda,\phi})\ge\varepsilon\right)\\
&\le 2\Pr\!\left(X-\frac{\phi^2}{\lambda}\ge\varepsilon\right).
\end{aligned}
```

Zero trailing diagonal entries in $`B_{\lambda,\phi}`$ are harmless. Each probability uses the appropriate estimator dimension. This is an absolute-error question, even when $`\mathop{\mathrm{tr}}\nolimits(A)=0`$.

<!-- canonical-target-end -->
