# RA-12 — exact mathematical and numerical specification

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

- Permanent ID: `RA-12`.
- Canonical README: `randomized-and-low-rank-approximation/RA-12/README.md`.
- Frozen repository revision: `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`.
- Source status at that revision: `Solved`.
- Existing-statement check: no `.lean` files under `randomized-and-low-rank-approximation/RA-12/`.

| Source file | Raw-byte SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-12/README.md` | `4771d76230e0a37ccf706b9d7fc0824d257856835d099465963cd200c0adb573` |
| `randomized-and-low-rank-approximation/RA-12/problem.tex` | `672cf44a491a97cb2217a4bd166e6ef980c0768a54d9d17992aa2c105e413e01` |
| `randomized-and-low-rank-approximation/RA-12/solution.md` | `297fda0345c6254c4248676cc19db4c1b0475adffafa2eb3b4d0e1de7d47cd67` |
| `randomized-and-low-rank-approximation/RA-12/solution.tex` | `155c3d4fd2ee034266cbd718bfedc0bb1f64ae4c55bbf87b1a6715f106a94de0` |

## Exact target and quantifier order

For every \(n\ge1\), nonzero real symmetric PSD \(A\in\mathbb R^{n\times n}\),
integer \(m\ge1\), and real \(\varepsilon\ge2/(m\mu)\), define
\[
\mu=\operatorname{tr}(A)/\|A\|_2,\qquad
B_\mu=\mu^{-1}\operatorname{diag}(I_{\lfloor\mu\rfloor},\mu-\lfloor\mu\rfloor).
\]
For \(X\sim\operatorname{Gamma}(m\mu/2,m\mu/2)\) in **shape/rate** convention,
the complete target is the conjunction
\[
\Pr(|T_m(A)-\operatorname{tr}A|\ge\varepsilon\operatorname{tr}A)
\le\Pr(|T_m(B_\mu)-1|\ge\varepsilon)
\]
and
\[
\Pr(|T_m(B_\mu)-1|\ge\varepsilon)\le\Pr(|X-1|\ge\varepsilon).
\]
Name both comparisons or export their explicit conjunction. Direct comparison
of first and last quantities omits the required middle extremizer.

## Concrete definitions of probabilities and matrices

For each real symmetric \(d\times d\) matrix \(D\), use the product probability
measure on \(m d\) real coordinates, all independently \(N(0,1)\). With row
vectors \(z_1,\ldots,z_m\),
\[
T_m(D)(z)=\frac1m\sum_{j=1}^m\sum_{p=1}^d\sum_{q=1}^d z_{jp}D_{pq}z_{jq}.
\]
Each estimator probability is the measure of its displayed event under
this **concrete joint product law**, in that estimator's own dimension.
A formulation on other probability spaces must explicitly require these
joint laws and justify distribution correspondence. Marginal Gaussian
assumptions alone are insufficient. No coupling between estimators is needed.
All event inequalities are non-strict.

Spectral norm is the Euclidean induced operator norm; trace is the diagonal
sum. PSD means symmetry and a nonnegative quadratic form. Derive
\(\|A\|_2>0\), \(\operatorname{tr}A>0\), and \(1\le\mu\le n\), rather than adding
new input restrictions. Set \(r=\lfloor\mu\rfloor\in\mathbb N\), and choose
extremizer dimension \(d_B=r+1\). Its first \(r\) diagonal entries are \(1/\mu\),
the last \((\mu-r)/\mu\), and all off-diagonal entries zero. Keep the zero
last entry at integer \(\mu\); it may give \(d_B=n+1\).

For positive real shape \(\alpha\) and rate \(\beta\), Gamma is the
Lebesgue-density probability measure
\[
g_{\alpha,\beta}(x)=
\begin{cases}\beta^\alpha x^{\alpha-1}e^{-\beta x}/\Gamma(\alpha)&x>0,\\0&x\le0.\end{cases}
\]
The final probability measures \(\{x:|x-1|\ge\varepsilon\}\) under this law.
Here mean is 1. Swapping rate and scale changes the target. Probabilities
can be nonnegative extended reals in Lean; any conversion to real values must
preserve exact order. No arbitrary probability functional may be assumed.

## Endpoints and complete source correspondence

Include \(m=1\), \(n=1\), integer/noninteger effective rank, rank deficiency,
zero padded eigenvalues, threshold equality, and tolerances with an empty
lower-tail event. Do not require positive definiteness, large \(m\), strict
threshold, rational spectra or bounded dimension.

The archived Stepaniants Theorem 1 states this exact chain. Its final bridge
sets \(\alpha=m/2\), \(w_i=\lambda_i(A)/\|A\|_2\), \(\rho=\alpha\mu\).
Then \(T_m(A)/\operatorname{tr}A\) has the law of \(Q_w/\rho\), with
independent \(\operatorname{Gamma}(\alpha,1)\) components, and threshold
\(\rho\varepsilon\ge1\). Lemma 3 controls both tails through the capped
coefficient extremizer, and Lemma 4 gives the Gamma endpoint. The Gaussian
rotational-invariance and chi-square/Gamma bridges must be established if
that normalized theorem is formalized. One tail, a mode bound, or an
unspecified larger threshold does not implement the complete original target.

Original source: Hallman, *Extremal bounds for Gaussian trace estimation*,
§5, Theorem 6 and Conjecture 3; [pinned v1](https://arxiv.org/html/2411.15454v1)
inspected 2026-09-28. Resolution: George Stepaniants, Department of Computing
and Mathematical Sciences, California Institute of Technology.
Colbrook's auxiliary counterexamples retain their separate original credit
and are not the target of this statement.

## Preimplementation review obligations

Inspect the joint Gaussian measure, dimension \(\lfloor\mu\rfloor+1\),
shape/rate order, both comparisons, non-strict threshold and all nonzero PSD
inputs. This target is mathematically specified. Reuse a Gamma-measure API
only after checking rate convention and support against the displayed
density. Numerical quadrature and spectrum sampling are unnecessary here.

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

For a real symmetric $`d\times d`$ matrix $`D`$ and integer $`m\ge1`$, define the Gaussian trace estimator

```math
T_m(D)=\frac1m\sum_{j=1}^{m}z_j^TDz_j,
\qquad z_1,\ldots,z_m\overset{\mathrm{iid}}{\sim}N(0,I_d).
```

Let $`A\ne0`$ be any real symmetric positive semidefinite $`n\times n`$ matrix, with $`n\ge1`$, and set

```math
\mu=\frac{\mathop{\mathrm{tr}}\nolimits(A)}{\|A\|_2},\qquad
B_\mu=\frac1\mu\mathop{\mathrm{diag}}\nolimits
\left(I_{\lfloor\mu\rfloor},\,\mu-\lfloor\mu\rfloor\right).
```

Here $`\|\cdot\|_2`$ is the spectral norm, $`\mu\ge1`$, and a zero final diagonal entry may be retained. Let $`X`$ have the Gamma distribution with shape and rate both $`m\mu/2`$. The shape/rate convention means that $`\mathop{\mathrm{Gamma}}\nolimits(\alpha,\beta)`$ has density $`\beta^\alpha x^{\alpha-1}e^{-\beta x}/\Gamma(\alpha)`$ for $`x>0`$.

**Conjecture.** For every such $`A`$, every integer $`m\ge1`$, and every $`\varepsilon\ge2/(m\mu)`$, the complete comparison chain holds:  

```math
\begin{aligned}
\Pr\!\left(
 |T_m(A)-\mathop{\mathrm{tr}}\nolimits(A)|
 \ge\varepsilon\mathop{\mathrm{tr}}\nolimits(A)
\right)
&\le \Pr\!\left(|T_m(B_\mu)-1|\ge\varepsilon\right)\\
&\le \Pr\!\left(|X-1|\ge\varepsilon\right).
\end{aligned}
```

Each estimator uses Gaussian vectors of its own matrix dimension; only their distributions are compared.

<!-- canonical-target-end -->
