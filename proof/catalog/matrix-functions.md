# Matrix functions and stability of matrix families

> Legacy source map and screening notes. Admitted statements have moved to category/problem folders. Follow the links below or [browse the new index](../../CATALOG.md). Shared notation and uncounted material are retained here as the historical source record.

This chapter contains twelve literature-screened problems. Difficulty and importance
are editorial judgments. An **open** status means the cited source poses the
question and the recorded follow-up search located no resolution; it is not a
proof that no solution exists. Dates below record searches, not mathematical
verification of open status. No solution is attempted here.

<a id="mf-01"></a>

## MF-01 — Optimal sign approximation with a multiplication budget

[Open the problem folder](../../matrix-functions-and-stability/MF-01/README.md) · [PDF](../../matrix-functions-and-stability/MF-01/problem.pdf) · [LaTeX](../../matrix-functions-and-stability/MF-01/problem.tex)


<a id="mf-02"></a>

## MF-02 — Multiplication overhead of cubic sign compositions

[Open the problem folder](../../matrix-functions-and-stability/MF-02/README.md) · [PDF](../../matrix-functions-and-stability/MF-02/problem.pdf) · [LaTeX](../../matrix-functions-and-stability/MF-02/problem.tex)


<a id="mf-03"></a>

## MF-03 — A uniform disk bound for wave-kernel Padé approximants

[Open the problem folder](../../matrix-functions-and-stability/MF-03/README.md) · [PDF](../../matrix-functions-and-stability/MF-03/problem.pdf) · [LaTeX](../../matrix-functions-and-stability/MF-03/problem.tex)


## Notation for MF-04–MF-07

Let $\mathcal H_d$ denote the nonempty compact subsets of
$\mathbb C^{d\times d}$. Use the spectral norm and its Hausdorff distance

$$
d_H(\mathcal M,\mathcal N)=\max\left\{
\sup_{A\in\mathcal M}\inf_{B\in\mathcal N}\|A-B\|_2,
\sup_{B\in\mathcal N}\inf_{A\in\mathcal M}\|A-B\|_2\right\}.
$$

The joint spectral radius is

$$
\widehat\rho(\mathcal M)=\lim_{k\to\infty}
\max_{A_1,\ldots,A_k\in\mathcal M}\|A_k\cdots A_1\|_2^{1/k}.
$$

These definitions also apply to finite real matrix sets. The ordinary spectral
radius of one matrix is written $\rho(A)$.

<a id="mf-04"></a>

## MF-04 — Finiteness for nonnegative rational matrix families

[Open the problem folder](../../matrix-functions-and-stability/MF-04/README.md) · [PDF](../../matrix-functions-and-stability/MF-04/problem.pdf) · [LaTeX](../../matrix-functions-and-stability/MF-04/problem.tex)


<a id="mf-05"></a>

## MF-05 — Local Hölder continuity of the joint spectral radius

[Open the problem folder](../../matrix-functions-and-stability/MF-05/README.md) · [PDF](../../matrix-functions-and-stability/MF-05/problem.pdf) · [LaTeX](../../matrix-functions-and-stability/MF-05/problem.tex)


<a id="mf-06"></a>

## MF-06 — A pointwise Lipschitz lower bound for the joint spectral radius

[Open the problem folder](../../matrix-functions-and-stability/MF-06/README.md) · [PDF](../../matrix-functions-and-stability/MF-06/problem.pdf) · [LaTeX](../../matrix-functions-and-stability/MF-06/problem.tex)


<a id="mf-07"></a>

## MF-07 — Uniform polynomial bounds for products at joint spectral radius one

[Open the problem folder](../../matrix-functions-and-stability/MF-07/README.md) · [PDF](../../matrix-functions-and-stability/MF-07/problem.pdf) · [LaTeX](../../matrix-functions-and-stability/MF-07/problem.tex)


<a id="mf-08"></a>

## MF-08 — NP-hardness of unrestricted static output-feedback stabilization

[Open the problem folder](../../matrix-functions-and-stability/MF-08/README.md) · [PDF](../../matrix-functions-and-stability/MF-08/problem.pdf) · [LaTeX](../../matrix-functions-and-stability/MF-08/problem.tex)


<a id="mf-09"></a>

## MF-09 — Decidability of strict stability for rational matrix families

[Open the problem folder](../../matrix-functions-and-stability/MF-09/README.md) · [PDF](../../matrix-functions-and-stability/MF-09/problem.pdf) · [LaTeX](../../matrix-functions-and-stability/MF-09/problem.tex)


<a id="mf-10"></a>

## MF-10 — Algebraicity of joint spectral radii from rational input

[Open the problem folder](../../matrix-functions-and-stability/MF-10/README.md) · [PDF](../../matrix-functions-and-stability/MF-10/problem.pdf) · [LaTeX](../../matrix-functions-and-stability/MF-10/problem.tex)


## Notation for MF-11–MF-12

For a compact nonempty $\mathcal M\subset\mathbb R^{d\times d}$ with
$\widehat\rho(\mathcal M)=1$, define its maximal product norm at length $k$ by

$$
g_{\mathcal M}(k)=\max_{A_1,\ldots,A_k\in\mathcal M}\|A_k\cdots A_1\|_2.
$$

These problems concern growth within one family over time. MF-07 instead requests
a dimension-dependent bound uniform across families.

<a id="mf-11"></a>

## MF-11 — Temporal regularity of marginal matrix-product growth

[Open the problem folder](../../matrix-functions-and-stability/MF-11/README.md) · [PDF](../../matrix-functions-and-stability/MF-11/problem.pdf) · [LaTeX](../../matrix-functions-and-stability/MF-11/problem.tex)


<a id="mf-12"></a>

## MF-12 — Realizing arbitrary polynomial growth exponents by finite matrix families

[Open the problem folder](../../matrix-functions-and-stability/MF-12/README.md) · [PDF](../../matrix-functions-and-stability/MF-12/problem.pdf) · [LaTeX](../../matrix-functions-and-stability/MF-12/problem.tex)


## Screened exclusions — not counted as open entries

- **Crouzeix's constant-two conjecture:** a recent proof claim was located:
  Lorist and Schwenninger,
  [A solution to Crouzeix's conjecture](https://arxiv.org/abs/2608.03841),
  submitted 4 August 2026. Excluded pending assessment of that claim; this catalog
  does not certify the proof or rely on older descriptions as evidence it is open.
- **Finiteness for pairs of 3×3 binary matrices:** covered by Theorem 3.1 of
  [Mejstrik's 2025 preprint](https://arxiv.org/pdf/2505.10178). It is not an
  additional open problem alongside MF-04.
- **Every degree-20 polynomial in five matrix products:** the older formulation
  in Jarlebring and Lorentzon,
  [The polynomial set associated with a fixed number of matrix-matrix multiplications](https://arxiv.org/html/2504.01500v3),
  Conjecture 11, requires reassessment against Sastre et al.,
  [Beyond Paterson–Stockmeyer: Advancing Matrix Polynomial Computation](https://wseas.com/journals/mathematics/2025/b385106-036%282025%29.pdf),
  §4 (2025), which gives a constructive claim, and its authors'
  [erratum notice](https://hipersc.blogs.upv.es/category/taylor-approximation/).
  Excluded rather than treating the older conjecture as current.
- **The workshop's sign-approximation equioscillation question:**
  [Problem 6.4](https://arxiv.org/html/2602.05394v3) uses an unspecified
  $\ell^2$ approximation measure/grid. The exact intended formulation needs
  clarification before it can satisfy this catalog's precision standard.
- **Integer-power growth for arbitrary real matrix families:** the general
  conjectures in Jungers, §3.6, Open Questions 3–4, cannot be retained.
  Protasov and Jungers,
  [Resonance and marginal instability of switching systems](https://arxiv.org/abs/1411.0497),
  gives sublinear-growth examples; Morris,
  [Marginally unstable discrete-time linear switched systems with highly irregular trajectory growth](https://arxiv.org/abs/2111.10225),
  gives irregular growth; and Varney and Morris,
  [On marginal growth rates of matrix products](https://arxiv.org/html/2209.00449),
  Corollary 6.1, gives a finite family with growth comparable to $k^{1/3}$.
  MF-11–MF-12 are later questions about the remaining possibilities.
