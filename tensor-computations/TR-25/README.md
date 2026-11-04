# TR-25 — Cohen–Macaulay coordinate rings for every tensor border-rank variety

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to specialist  
**Status:** Solved  
**Last checked:** 2026-11-04

**Rating rationale:** An all-format theorem would overcome longstanding obstructions in the local algebra of secant varieties and encompass other major Cohen–Macaulay conjectures. The depth and resolution questions chiefly concern specialists in tensor algebraic geometry. These ratings are historical and refer to the original universal question, which is resolved negatively below. They do not rate the questions that remain open.

## Resolution — 4 November 2026

**Resolved negatively.** Wenqi Zhu (University of Oxford) and Ping Nie
(University of Waterloo).

The answer is **no**. For $`k=3`$, $`(n_1,n_2,n_3)=(3,4,5)`$ and $`r=5`$,
the variety $`X_5\subseteq\mathbb C^3\otimes\mathbb C^4\otimes\mathbb C^5`$
has dimension $`50`$, and its coordinate ring $`A_5=S/I(X_5)`$ satisfies

```math
\mathop{\mathrm{depth}}\nolimits(A_5)_{\mathfrak m}
<50=\dim(A_5)_{\mathfrak m},
```

so $`A_5`$ is not Cohen–Macaulay. This is the case $`X_5(3,4,5)`$ of
Corollary 1.2, stated on p. 2 of the 42-page paper
[*Secant Varieties of Segre Products Need Not Be Cohen–Macaulay*](https://github.com/erenup/segre-secant-cohen-macaulay/blob/3d8b1586b4e6e7ee7164116711aced9f7a23a057/paper/main.pdf)
at the immutable
[revision `3d8b158`](https://github.com/erenup/segre-secant-cohen-macaulay/tree/3d8b1586b4e6e7ee7164116711aced9f7a23a057),
made public on 4 November 2026. Up to the order of the factors, it is the
smallest format in the range of Theorem 1.1 (p. 1): for all integers

```math
r\geq5,\qquad a,b\geq3,\qquad a+b\geq r+2,\qquad c\geq r,
```

and after any permutation of the three factors, the reduced affine variety
$`X_r(a,b,c)\subseteq\mathbb C^a\otimes\mathbb C^b\otimes\mathbb C^c`$ of
tensors of border rank at most $`r`$ has dimension $`D=r(a+b+c-2)`$, fails
Serre's condition $`S_2`$, is not Cohen–Macaulay, and has depth less than
$`D`$ at its homogeneous maximal ideal. Corollary 1.2 also lists
$`X_5(6,6,6)`$, of dimension $`80`$, the varieties $`X_r(3,r-1,r)`$ of
dimension $`2r^2`$, and the unit-tensor orbit closures
$`X_r(r,r,r)=\overline{\mathrm{GL}_r(\mathbb C)^3\cdot\Delta_r}`$, with
$`\Delta_r=\sum_{i=1}^re_i\otimes e_i\otimes e_i`$, for every $`r\geq5`$.

In format $`3\times4\times5`$ the witness is the integer tensor
$`T=\sum_{i=1}^5Q_i\otimes f_i`$ of equation (4.5) (p. 10), padded with zeros
from $`3\times3\times5`$. Here $`Q_1,\ldots,Q_6`$ are the rank-one
$`3\times3`$ matrices formed from the rows and the negated columns of
$`M=(j^{i-1})_{1\leq i,j\leq3}`$, and their only linear relation is
$`Q_1+\cdots+Q_6=0`$ (Lemma 4.1, p. 10). That relation gives a second
five-term decomposition (4.7). By Proposition 4.6 (p. 13), $`T`$ has rank and
border rank five and both decompositions have injective addition
differentials. Section 2 (pp. 3–8) constructs a smooth birational space of
decompositions with an open subset that maps into the smooth locus and has a
complement of codimension at least two (Proposition 2.5, p. 7). The
two-point conductor obstruction of Proposition 3.3 (p. 9) then shows that the
local ring at $`T`$ is not $`S_2`$: the two decompositions give two distinct
normalization charts over $`T`$, and $`S_2`$ would force a conductor divisor
that the codimension bound excludes. Section 5 (pp. 14–15) passes to the
vertex: if $`(A_r)_{\mathfrak m}`$ were Cohen–Macaulay, a graded free
resolution and the Auslander–Buchsbaum formula would make every local ring
Cohen–Macaulay.

**Comparison with the target.** The target asserts Cohen–Macaulayness for
every $`k\geq3`$, all $`n_1,\ldots,n_k\geq1`$ and every $`r\geq1`$, so one
non-Cohen–Macaulay instance refutes it. The paper's $`X_r(a,b,c)`$ (equation
(1.1), p. 1) is the Zariski closure of the sums of $`r`$ pure tensors in
$`\mathbb C^a\otimes\mathbb C^b\otimes\mathbb C^c`$ with its reduced
structure, so it is the affine cone and contains the zero tensor. Its
coordinate ring is $`S/I(X_r)`$, and $`\mathfrak m`$ is its ideal of
positive-degree elements. These are the definitions of the problem statement
with $`k=3`$ and $`(n_1,n_2,n_3)=(a,b,c)`$, over the same field
$`\mathbb C`$. Since Theorem 1.1 holds after permuting the factors, the order
of $`(3,4,5)`$ is immaterial. Corollary 1.3 (p. 2) gives the projective
statement: $`\sigma_r(\mathrm{Seg}(\mathbb P^{a-1}\times\mathbb P^{b-1}\times\mathbb P^{c-1}))`$
has a non-Cohen–Macaulay local ring at the class of the witness, so it is
neither locally nor arithmetically Cohen–Macaulay. Section 1.1 (p. 2) notes
that Conjecture 1.1 of reference 1 and Conjecture 3.32 of reference 2 concern
the ordinary reduced secant varieties, with neither a conciseness condition
nor a restriction to balanced formats, and that Theorem 1.1 refutes them with
the same field, reduced structure and projective embedding.

The unit-tensor orbit closures $`X_r(r,r,r)`$ were already known to be
nonnormal for every $`r\geq5`$, by Bürgisser and Ikenmeyer (Corollary 7.2(2)
of arXiv:1011.1350v1 and Corollary 5.26 of arXiv:1511.02927v2), as cited in
Section 1.2 (pp. 2–3). Nonnormality does not imply failure of $`S_2`$ or of
Cohen–Macaulayness; the paper's example is the Cohen–Macaulay, nonnormal
domain $`\mathbb C[t^2,t^3]`$. As the paper states, Theorem 1.1 strengthens
the known nonnormality of these orbit closures to failure of $`S_2`$ and of
Cohen–Macaulayness, and the proof does not use the nonnormality results. In
reference 2, implications run from the universal conjecture to
Cohen–Macaulayness assertions for surface Quot schemes and smoothable Hilbert
scheme components. Section 6.4 (pp. 18–19) notes that its failure gives no
counterexample to these assertions or to Haiman's isospectral Hilbert scheme
conjecture; Propositions 6.3 and 6.4 (pp. 17–18) show that the mechanism
cannot occur on invertible-slice charts and that the witness lifts to smooth
points of the concise secant. The counterexample refutes only the
universal assertion. It does not decide Cohen–Macaulayness in formats and
ranks outside Theorem 1.1, apart from the extensions below.

**Extensions.** In the other direction, Proposition 6.2 (p. 16) shows that
$`X_5(3,3,c)`$ is Cohen–Macaulay for every $`c\geq1`$: it is the whole space
for $`c\leq5`$ and the variety of $`9\times c`$ matrices of rank at most five
for $`c\geq5`$. Section 7 (pp. 19–40) describes the normalization near
explicit witnesses. Corollary 7.3 (p. 20) gives exactly six reduced, smooth
normalization points over the rank-five witness for all $`a,b\geq3`$,
$`a+b\geq7`$ and $`c\geq5`$, and Theorems 7.6, 7.8 and 7.9 (pp. 22–26) give
exact smooth fibres of six, seven and $`r+1`$ points over higher-rank
witnesses. Theorem 7.10 (p. 27) presents the completed local ring at the
rank-five witness, with dimension $`5(a+b+c-2)`$ and depth $`3a+3b+5c+3`$; in
format $`3\times4\times5`$ these are $`50`$ and $`49`$ (Remark 7.11, p. 30).
Theorems 7.12–7.14 (pp. 31–32) give the normalization fibres and the local
models of their boundary points for one-sided extensions and for two
specified mixed extensions. These results concern the displayed witnesses.

**What remains open.** The paper determines neither the depth at the
homogeneous vertex nor, for $`r\geq6`$, the depth at the witness (p. 2;
Remark 7.11, p. 30). It makes no minimal-format assertion (pp. 3 and 17), and
formats outside the theorem, such as $`X_5(3,4,4)`$ and $`X_5(4,4,4)`$, in
which no factor has dimension at least five, are not decided. Theorem 6.1
(p. 15) shows that no three-factor tensor has two distinct immersive
$`r`$-term decompositions when $`r\leq4`$, so the mechanism first occurs at
rank five; this does not decide Cohen–Macaulayness for $`r\leq4`$ (p. 16).
The paper gives no classification of the Cohen–Macaulay border-rank
varieties, none in order $`k\geq4`$, and no Cohen–Macaulay or
rational-singularity assertion about their normalizations (pp. 3 and 19).

**Proof and verification scope.** Theorem 1.1, its corollaries and the
extensions are proved in the written paper. A Lean formalization at the same
revision proves exactly two finite certificate layers, in two pinned projects
using only the standard axioms. `TR25.finiteCertificate`, recorded in its
[Lean guide](https://github.com/erenup/segre-secant-cohen-macaulay/blob/3d8b1586b4e6e7ee7164116711aced9f7a23a057/lean/witness-666/README.md),
covers the $`3\times3\times5`$ integer witness and its zero padding to
$`6\times6\times6`$: both decompositions with nonzero, pairwise
nonproportional summands and different directions, third flattening rank
five, the six rational determinant values in (4.11) and (4.12), and coordinate
Jacobian ranks $`45`$ and $`80`$. `TR25Family.finiteCertificate`, recorded in
its [Lean guide](https://github.com/erenup/segre-secant-cohen-macaulay/blob/3d8b1586b4e6e7ee7164116711aced9f7a23a057/lean/family-345/README.md),
covers the witness in format $`3\times4\times5`$: both decompositions,
flattening ranks $`3,3,5`$, the pair-product and third-factor ranks, the six
determinant values and both coordinate Jacobian ranks $`50`$. Neither
formalizes border rank, the dimension of the secant variety, the geometric
tangent spaces, normalization, the conductor argument, $`S_2`$,
Cohen–Macaulayness, any depth statement (vertex or local) or the family for
all ranks and formats. No numbered result of the paper is a Lean theorem in full, and no
Lean theorem states the failure of Cohen–Macaulayness, so this is not a Lean
verification of the target. The
[verification record](https://github.com/erenup/segre-secant-cohen-macaulay/blob/3d8b1586b4e6e7ee7164116711aced9f7a23a057/VERIFICATION.md)
also describes exact checks of the witness calculations, of the finite cores
of the Section 7 results and of 31 pairs of family decompositions, which
certify finite calculations and do not establish the theorem.

**Review.** Solved by independent informal AI-agent audits: two reports, by
different referees, on each written result (the $`6\times6\times6`$ case, the family
theorem, the normalization fibres, the higher-rank fibres, the completed
local ring and the one-sided and mixed boundary models), reports on the
statement and on the proof of each Lean certificate, and reports on three
earlier drafts of the paper; none requested a mathematical correction. The
[review record](https://github.com/erenup/segre-secant-cohen-macaulay/blob/3d8b1586b4e6e7ee7164116711aced9f7a23a057/verification/reviews/README.md)
contains the audit reports and records their scope and its independence
caveats. The
paper discloses its use of AI tools. The catalogue did not rerun the Lean or
exact checks.

The retained status check below predates this resolution.

## Problem statement

Fix integers $`k\geq3`$, $`n_1,\ldots,n_k\geq1`$, and $`r\geq1`$. In
$`V=\mathbb C^{n_1}\otimes\cdots\otimes\mathbb C^{n_k}`$, let

```math
X_r=\overline{\left\{
\sum_{\ell=1}^{r}v_{1,\ell}\otimes\cdots\otimes v_{k,\ell}:
v_{i,\ell}\in\mathbb C^{n_i}
\right\}}^{\,\mathrm{Zar}}.
```

Let $`S=\mathbb C[V]`$ be the polynomial ring in the tensor entries, let $`I(X_r)`$ be its vanishing ideal, and let $`A_r=S/I(X_r)`$.

Is $`A_r`$ Cohen–Macaulay for every such format and rank threshold?

Explicitly, if $`\mathfrak m`$ is the ideal of positive-degree elements of $`A_r`$, the requested equality is

```math
\mathop{\mathrm{depth}}\nolimits(A_r)_{\mathfrak m}
=\dim(A_r)_{\mathfrak m}.
```

Depth is the maximum length of a regular sequence in the maximal ideal: each successive element is a non-zero-divisor after quotienting by its predecessors. Dimension is Krull dimension. This is Oeding's conjecture that all secant varieties of Segre products are arithmetically Cohen–Macaulay. The zero tensor is retained by using the affine cone.

## Why it matters

These are the algebraic sets underlying low-border-rank tensor approximation. Cohen–Macaulayness constrains their equations and free resolutions, supporting the determination of generators and the analysis of degeneracies. The conjecture does not assert that exact low-rank tensor approximation is computationally easy or always attained.

## References and status check

1. L. Oeding, *Are all Secant Varieties of Segre Products Arithmetically Cohen-Macaulay?*, [Preprint (2016), v2](https://arxiv.org/pdf/1603.08980v2), Conjecture 1.1, p.1; §2 collects established cases.
2. J. Jagiełła and J. Jelisiejew, *Unrestrictions and concise secant varieties*, [2026 preprint, v2](https://arxiv.org/html/2604.24879v2), Conjecture 3.32 and its surrounding discussion; §1.5.3 explains a connection to the Salmon ideal problem.

### Status check — 2026-09-10

Checked Oeding v2, including Theorems 3.1–3.2 and Proposition 3.5, and Jagiełła–Jelisiejew v2, Conjecture 3.32, with targeted later-resolution searches. Oeding proves substantive tensor cases, including the fourth secant of $`\mathbb P^2\times\mathbb P^2\times\mathbb P^n`$ for $`n\ge3`$, rather than only the matrix or rank-one cases. The June 2026 source still treats the all-format conjecture as open. Inheritance results require extra hypotheses and do not establish it universally. No full proof or counterexample was located.
