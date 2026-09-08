# Matrix functions and stability of matrix families

This chapter contains twelve literature-screened problems. Difficulty and importance
are editorial judgments. An **open** status means the cited source poses the
question and the recorded follow-up search located no resolution; it is not a
proof that no solution exists. Dates below record searches, not mathematical
verification of open status. No solution is attempted here.

<a id="mf-01"></a>

## MF-01 — Optimal sign approximation with a multiplication budget

- **Difficulty:** challenging
- **Importance:** interesting to the community
- **Status:** open; explicit 2026 problem
- **Last checked:** 2026-09-08

**Statement.** For $m\in\mathbb N_0$ and $0<\delta<1$, put

$$
I_\delta=[-1,-\delta]\cup[\delta,1].
$$

Let $\mathcal P_m$ consist of real polynomials computed from $1,x$ by
straight-line programs using at most $m$ nonscalar multiplications; real linear
combinations cost nothing. Define

$$
E_m(\delta)=\inf_{p\in\mathcal P_m}
\max_{x\in I_\delta}|p(x)-\operatorname{sign}(x)|.
$$

Determine matching asymptotic upper and lower bounds for $E_m(\delta)$, with
the dependence on both $m$ and $\delta$ explicit. Infima avoid assuming
attainment. The arithmetic model concerns a single polynomial identity valid for
matrices of every size.

**References and status evidence.** Amsel et al.,
[Linear Systems and Eigenvalue Problems: Open Questions from a Simons Workshop](https://arxiv.org/html/2602.05394v3),
§6.3, Problem 6.3 (2026). Rubensson, Jarlebring and Lorentzon,
[Recursive expansion of the matrix step function using polynomials of degree eight](https://arxiv.org/html/2606.24701v1),
§7 (June 2026), still identifies optimal recursive expansion as open. Its
particular algorithm does not establish the unrestricted optimum above.

<a id="mf-02"></a>

## MF-02 — Multiplication overhead of cubic sign compositions

- **Difficulty:** challenging
- **Importance:** interesting to the community
- **Status:** open; explicit 2026 problem
- **Last checked:** 2026-09-08

**Statement.** With $I_\delta,E_m$ as in MF-01, define

$$
C_T(\delta)=\inf_{a_t,b_t\in\mathbb R}
\max_{x\in I_\delta}|(q_T\circ\cdots\circ q_1)(x)-\operatorname{sign}(x)|,
\qquad q_t(x)=a_tx+b_tx^3.
$$

Determine the asymptotic dependence on $m,\delta$ of

$$
T_{\min}(m,\delta)=\inf\{T\in\mathbb N_0:C_T(\delta)\le E_m(\delta)\},
$$

where the empty composition is $x$ and $\inf\varnothing=+\infty$.
Each stage costs at most two matrix products.

**References and status evidence.** Amsel et al.,
[Simons workshop report](https://arxiv.org/html/2602.05394v3), §6.3, Problem 6.5.
Rubensson, Jarlebring and Lorentzon,
[degree-eight recursive expansion](https://arxiv.org/html/2606.24701v1), §7,
provides a June 2026 follow-up discussion; it does not settle this comparison.

**Scope.** MF-01 asks for an optimum value over general evaluation programs.
This problem measures the price of a particular, reusable composition architecture;
the two tasks are related but have different requested outputs.

<a id="mf-03"></a>

## MF-03 — A uniform disk bound for wave-kernel Padé approximants

- **Difficulty:** hard
- **Importance:** interesting to specialist
- **Status:** open; original conjecture plus a search for subsequent resolution
- **Last checked:** 2026-09-08

**Statement.** Let

$$
f(z)=\sum_{j=0}^\infty\frac{z^j}{(2j)!}=\cosh\sqrt z,
$$

where the series defines the entire function without a square-root branch choice.
For each integer $m\ge1$, let $r_m=P_m/Q_m$ be its diagonal Padé
approximant at zero: $\deg P_m,\deg Q_m\le m$, $Q_m(0)=1$, and
$Q_m(z)f(z)-P_m(z)=O(z^{2m+1})$. Is it true that the reduced rational
function $r_m$ has no pole in $\{z\in\mathbb C:|z|\le3\}$ and

$$
|1-r_m(z)|\le2\qquad (|z|\le3)
$$

for every $m$?

**Reference and status evidence.** Nadukandi and Higham,
[Computing the Wave-Kernel Matrix Functions](https://eprints.maths.manchester.ac.uk/2651/3/manuscript_nadukandi_higham_wkm_2018_08_01.pdf),
SIAM J. Scientific Computing 40(6) (2018),
[DOI](https://doi.org/10.1137/18M1170352), §4.2, Conjecture 4.6,
manuscript p. 12. Lemma 4.5 establishes the finite range $m\le20$;
§4.3 explains its role in backward-error analysis. Searches for the paper title
with “conjecture” and for “Conjecture 4.6” with “cosh” and “Padé” located no
general proof or counterexample. The status evidence is therefore weaker than a
recent paper explicitly reaffirming the conjecture.

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

- **Difficulty:** extreme
- **Importance:** broadly interesting
- **Status:** open; explicitly retained in a 2025 follow-up
- **Last checked:** 2026-09-08

**Statement.** Does every finite nonempty set
$\mathcal M\subset\mathbb Q_{\ge0}^{d\times d}$, for every positive integer
$d$, admit a positive integer $k$ and matrices
$A_1,\ldots,A_k\in\mathcal M$ such that

$$
\widehat\rho(\mathcal M)=\rho(A_k\cdots A_1)^{1/k}?
$$

The entries must be nonnegative rationals; unrestricted real entries change the
status. This asks whether a finite product realizes the asymptotic growth rate.

**References and status evidence.** Jungers and Blondel,
[On the finiteness property for rational matrices](https://arxiv.org/abs/math/0702489),
Linear Algebra Appl. 428 (2008), 2283–2295,
[DOI](https://doi.org/10.1016/j.laa.2007.07.007), abstract and reduction theorems;
Jungers, *The Joint Spectral Radius: Theory and Applications*,
[Chapter 4](https://doi.org/10.1007/978-3-540-95980-9_5), pp. 63–74 (2009).
They reduce this question to pairs of binary matrices in arbitrary dimension.
Mejstrik,
[The finiteness conjecture for 3×3 binary matrices](https://arxiv.org/pdf/2505.10178),
§3 and Theorem 3.1 (2025 preprint), treats the all-dimensions problem as open
while proving the binary-pair case in dimension three. Searches for rational
finiteness and binary-pair counterexamples through the check date found no
resolution of the general question. Equivalent binary formulations count once.

<a id="mf-05"></a>

## MF-05 — Local Hölder continuity of the joint spectral radius

- **Difficulty:** challenging
- **Importance:** interesting to the community
- **Status:** open; Conjecture L1 in the source below
- **Last checked:** 2026-09-08

**Statement.** For every $d\ge1$ and $\mathcal M_0\in\mathcal H_d$, do
there exist $r,C>0$ such that

$$
|\widehat\rho(\mathcal M)-\widehat\rho(\mathcal N)|
\le C d_H(\mathcal M,\mathcal N)^{1/d}
$$

whenever $d_H(\mathcal M,\mathcal M_0)<r$ and
$d_H(\mathcal N,\mathcal M_0)<r$?

**Reference and status evidence.** Epperlein and Wirth,
[The joint spectral radius is pointwise Hölder continuous](https://arxiv.org/html/2311.18633v2),
Linear Algebra Appl. 704 (2025), 92–122,
[DOI](https://doi.org/10.1016/j.laa.2024.09.016), §2, Conjecture 3 (L1).
Pointwise results in that paper do not prove this local assertion.

<a id="mf-06"></a>

## MF-06 — A pointwise Lipschitz lower bound for the joint spectral radius

- **Difficulty:** challenging
- **Importance:** interesting to the community
- **Status:** open; Conjecture P2 in the source below
- **Last checked:** 2026-09-08

**Statement.** For every $d\ge1$ and $\mathcal M\in\mathcal H_d$, do
there exist $r,C>0$ such that

$$
\widehat\rho(\mathcal N)\ge\widehat\rho(\mathcal M)-C d_H(\mathcal M,\mathcal N)
\quad\text{if }d_H(\mathcal M,\mathcal N)<r?
$$

**Reference and status evidence.** Epperlein and Wirth,
[The joint spectral radius is pointwise Hölder continuous](https://arxiv.org/html/2311.18633v2),
§2, Conjecture 3 (P2). The conjectured exponent is one.

**Scope.** The reference family is fixed while the perturbed family varies. An
answer controls how rapidly a stability diagnostic can decrease under data error;
MF-05 instead requires a two-sided estimate uniform over two varying families.

<a id="mf-07"></a>

## MF-07 — Uniform polynomial bounds for products at joint spectral radius one

- **Difficulty:** challenging
- **Importance:** interesting to the community
- **Status:** open; Conjecture L3 in the source below
- **Last checked:** 2026-09-08

**Statement.** Does each $d\ge1$ admit $\Theta_d>0$ such that every
$\mathcal M\in\mathcal H_d$ with $\widehat\rho(\mathcal M)=1$ satisfies

$$
\|A_k\cdots A_1\|_2\le\Theta_d(Lk)^{d-1},\qquad
L=\max_{A\in\mathcal M}\|A\|_2,
$$

for all $k\ge1$ and all $A_1,\ldots,A_k\in\mathcal M$?

**Reference and status evidence.** Epperlein and Wirth,
[The joint spectral radius is pointwise Hölder continuous](https://arxiv.org/html/2311.18633v2),
§2, Conjecture 3 (L3). Lemma 27 proves dimension two. The constant above must
be independent of the family.

**Common follow-up screen for MF-05–MF-07.** Searches combining “joint spectral
radius” with “local Hölder”, “Lipschitz lower”, “trajectory bounds”, the authors'
names, and 2025/2026 found no later resolution. These searches supplement the
explicit 2025 conjectures; they do not establish exhaustiveness. The three entries
are separately named assertions in the source, not a count of dimensional cases.

<a id="mf-08"></a>

## MF-08 — NP-hardness of unrestricted static output-feedback stabilization

- **Difficulty:** extreme
- **Importance:** broadly interesting
- **Status:** open; longstanding complexity question, with related variants separated
- **Last checked:** 2026-09-08

**Statement.** Consider the decision language whose inputs are rational matrices
$A\in\mathbb Q^{n\times n}$, $B\in\mathbb Q^{n\times m}$, and
$C\in\mathbb Q^{p\times n}$, with positive dimensions included in the input.
The answer is yes precisely when there exists an unrestricted real matrix
$K\in\mathbb R^{m\times p}$ for which

$$
\operatorname{Re}\lambda<0\qquad\text{for every }\lambda\in\sigma(A+BKC).
$$

Is this language NP-hard under polynomial-time many-one reductions in the binary
encoding of the rational input? The requested output is a complexity theorem,
not another numerical heuristic for finding $K$.

**References and status evidence.** Minyue Fu,
[Two Challenging Problems in Control Theory](https://www.eng.newcastle.edu.au/~mf140/home/Papers/Fu_UTSC.pdf),
§3, pp. 3–7, defines strict Hurwitz stabilization and distinguishes it from the
known NP-hard problem with entrywise bounds on $K$ (§3.1). Gillis and Sharma,
[Solving matrix nearness problems via Hamiltonian systems, matrix factorization, and optimization](https://arxiv.org/pdf/2202.02618),
§3.5.2, pp. 50–51 (2022 manuscript), reiterates the unresolved complexity of
static output feedback. Its broader stability convention should not replace the
strict inequality above. Follow-up searches for unrestricted stabilization
NP-hardness found no resolving reduction; claims about arbitrary bilinear matrix
inequalities or prescribed pole placement do not by themselves settle this
language. No claim of NP membership is made.

<a id="mf-09"></a>

## MF-09 — Decidability of strict stability for rational matrix families

- **Difficulty:** extreme
- **Importance:** broadly interesting
- **Status:** open; book question with subsequent-literature screening
- **Last checked:** 2026-09-08

**Statement.** Does a Turing machine exist which, on every input consisting of a
finite nonempty list of matrices in $\mathbb Q^{d\times d}$, encoded by binary
integer numerators and positive denominators, halts and correctly decides whether

$$
\widehat\rho(\mathcal M)<1?
$$

Dimension and list length are part of the input. No separation from the threshold
is promised. The question asks for termination and correctness, without a
polynomial running-time requirement.

**References and status evidence.** Jungers,
[*The Joint Spectral Radius: Theory and Applications*](https://perso.uclouvain.be/raphael.jungers/sites/default/files/kcfinder/files/book.pdf),
§2.2.3, Open Question 1, printed p. 29 of the author manuscript. Blondel and Tsitsiklis,
[The boundedness of all products of a pair of matrices is undecidable](https://www.sciencedirect.com/science/article/abs/pii/S0167691100000499),
Systems & Control Letters 41 (2000), 135–140, §2, proves undecidability of
the non-strict test $\widehat\rho\le1$. That theorem does not answer the
strict test.

The screen included “joint spectral radius” with “strict”, “decidability”,
“less than one”, and 2025/2026. No deciding algorithm or applicable undecidability
reduction was located. Some later literature summarizes the non-strict theorem
as a generic stability impossibility; admission here follows its actual threshold.
MF-04 is a proposed finite-product property, whereas this entry asks for a decision
procedure even if such a property fails.

<a id="mf-10"></a>

## MF-10 — Algebraicity of joint spectral radii from rational input

- **Difficulty:** extreme
- **Importance:** interesting to the community
- **Status:** open; book question with subsequent-literature screening
- **Last checked:** 2026-09-08

**Statement.** Is it true that, for every $d\ge1$ and every finite nonempty
$\mathcal M\subset\mathbb Q^{d\times d}$, there exists a nonzero polynomial
$p\in\mathbb Z[t]$ such that

$$
p\bigl(\widehat\rho(\mathcal M)\bigr)=0?
$$

The claim is about the value being algebraic; it does not assert a uniform
procedure for finding its minimal polynomial.

**Reference and status evidence.** Jungers,
[*The Joint Spectral Radius: Theory and Applications*](https://perso.uclouvain.be/raphael.jungers/sites/default/files/kcfinder/files/book.pdf),
§4.4, Open Question 7, printed p. 75 of the author manuscript.
Searches combining “joint spectral radius”, “rational matrices”, “algebraic
number”, “algebraicity”, and “transcendental” located no proof or rational-input
counterexample. The latest explicit formulation located remains the book.

**Scope.** Both signs are permitted. A finite-product formula would imply
algebraicity for its particular input, but this question requires no such formula.
It concerns exact representation of a matrix computation's output, separately
from the geometry of the set of all stable inputs.

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

- **Difficulty:** challenging
- **Importance:** interesting to specialist
- **Status:** open; two-part question retained as one entry
- **Last checked:** 2026-09-08

**Statement.** Does every family in the preceding notation satisfy both

$$
\exists c>0\ \forall k,\ell\ge1:\quad
g_{\mathcal M}(k+\ell)\ge c\,g_{\mathcal M}(k)
$$

and

$$
\forall \ell\ge1\ \exists C_\ell>0\ \forall k\ge1:\quad
g_{\mathcal M}(\ell k)\le C_\ell\,g_{\mathcal M}(k)?
$$

Constants may depend on $\mathcal M$.

**Reference and status evidence.** Varney and Morris,
[On marginal growth rates of matrix products](https://arxiv.org/html/2209.00449),
Linear Algebra Appl. 709 (2025), 132–163,
[DOI](https://doi.org/10.1016/j.laa.2025.01.013), §4, Definition 4.1 and §7,
Question 1. The source names these properties weak increase and weak upper regular
variation. Searches for both property names, the authors, and subsequent
matrix-product growth papers located no resolution.

<a id="mf-12"></a>

## MF-12 — Realizing arbitrary polynomial growth exponents by finite matrix families

- **Difficulty:** challenging
- **Importance:** interesting to the community
- **Status:** open; explicit question in a 2025 journal paper
- **Last checked:** 2026-09-08

**Statement.** For every real $\alpha\ge0$, do there exist a positive integer
$d$, a finite nonempty $\mathcal M\subset\mathbb R^{d\times d}$ with
$\widehat\rho(\mathcal M)=1$, and constants $0<c\le C<\infty$ such that

$$
c k^\alpha\le g_{\mathcal M}(k)\le C k^\alpha
\qquad\text{for every integer }k\ge1?
$$

**Reference and status evidence.** Varney and Morris,
[On marginal growth rates of matrix products](https://arxiv.org/html/2209.00449),
§7, Question 2. Corollary 6.1 realizes exponent $1/3$; the all-exponents question
remains posed. Searches for the title, authors, and marginal-growth exponents
through 2026 located no complete answer. Infinite compact families and
subsequence-only lower bounds do not meet the finite-family, every-length target.

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
