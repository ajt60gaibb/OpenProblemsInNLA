# IE-26 — Sharp stability bounds for perturbed Fourier interpolation

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Topic:** Conditioning of Fourier matrices and interpolation operators  
**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Solved  
**Last checked:** 2026-09-12

**Rating rationale:** The conjectures ask for sharp dimension dependence under a fixed relative perturbation of every sampling point. They concern the sensitivity of Fourier coefficient recovery and interpolation, with consequences for spectral computation and nonuniform sampling.

## Resolution — 12 September 2026

**Solved affirmatively.** [Theorem 1 and Sections 2–7 of the complete proof](solution.md) establish both original bounds: the Lebesgue estimate with one absolute constant for every $`0<\alpha<1/2`$, and the normalized square Fourier inverse-norm estimate without a logarithmic loss for each fixed $`1/4<\alpha<1/2`$. Every $`N\ge2`$ and every allowed collection of shifts is included. The second constant may depend on $`\alpha`$; no endpoint assertion at $`\alpha=1/4`$ is made.

**Author:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. [Proof PDF](solution.pdf) · [Standalone TeX](solution.tex).

The full argument passed a separate [independent Codex-agent mathematical review](../../references/stepaniants-ie26-2026-09-12/verification/independent-review/IE-26-independent-review.md), bound to the exact frozen source. The coordinating agent contributed before freeze and is recorded separately, not as the independent reviewer. Substantial AI assistance is disclosed; no external human peer review or formal verification is asserted.

Austin and Trefethen retain credit for the conjectures and prior analysis, with the related thesis and later results cited below. The periodic Hilbert-transform weak $`(1,1)`$ inequality is the external analytic input; the proof supplies the remaining grid and matrix estimates. The [submission and verification record](../../references/stepaniants-ie26-2026-09-12/README.md) contains exact provenance and the bounded public eligibility check. The original target, earlier evidence and references remain below. The ratings above describe the former open question.

## Statement

For each integer $`N\ge2`$, put $`m=2N+1`$ and $`h=2\pi/m`$. Fix $`0<\alpha<1/2`$, choose arbitrary real numbers $`s_{-N},\ldots,s_N`$ with $`|s_k|\le\alpha`$, and put $`x_k=(k+s_k)h`$, interpreted modulo $`2\pi`$. Define the normalized Fourier matrix

```math
F_N(s)=m^{-1/2}[e^{ijx_k}]_{k,j=-N}^{N}.
```

The nodes are distinct. For $`y\in\mathbb C^m`$, let $`T_Ny`$ be the unique trigonometric polynomial of degree at most $`N`$ with $`(T_Ny)(x_k)=y_k`$. Set

```math
\Lambda_N(s)=\sup_{\|y\|_\infty\le1}\|T_Ny\|_{L^\infty[-\pi,\pi]},\qquad
\Gamma_N(s)=\|F_N(s)^{-1}\|_2.
```

**Austin–Trefethen conjectures.** Establish the following two uniform bounds:

1. There is an absolute $`C>0`$ such that, for every $`N\ge2`$, $`0<\alpha<1/2`$, and admissible $`s`$,

   $`\displaystyle \Lambda_N(s)\le C\frac{N^{2\alpha}-1}{\alpha(1-2\alpha)}.`$

2. For every fixed $`1/4<\alpha<1/2`$, there is $`C_\alpha>0`$, independent of $`N`$ and $`s`$, such that

   $`\displaystyle \Gamma_N(s)\le C_\alpha N^{4\alpha-1}.`$

These are kept together as one perturbed-grid stability target. The first is the source's conjectured replacement in equation (12); the second is its conjecture on p.2119. The normalized matrix makes the discrete norm convention explicit, following equation (1.6) of Chen–Lin–Zhang. The second statement does not assert an endpoint bound at $`\alpha=1/4`$. The first has the usual logarithmic limit as $`\alpha\downarrow0`$.

## Evidence and relation between the bounds

Austin's thesis, Conjecture 3.5, states the first bound with a universal constant and predicts a matching worst-grid growth rate. Conjecture 3.10 concerns the second norm. This is finite-dimensional conditioning of an interpolation map, rather than restricted isometry of column subsets of an equispaced Fourier matrix as in [FR-02](../../frames-and-matrix-designs/FR-02/README.md).

Chen–Lin–Zhang's August 2026 preprint gives

```math
\Gamma_N(s)\le C_\alpha N^{4\alpha-1}\log N
```

for $`1/4<\alpha<1/2`$, together with a family having a matching lower power $`N^{4\alpha-1}`$. Thus the logarithmic factor remains in the checked upper bound. The discrete Kadec theorem of Yu–Townsend treats $`\alpha<1/4`$, outside the second displayed target; oversampling treats a rectangular matrix instead of the square matrix here. Norm conversion alone loses powers of $`N`$ and does not identify the two conjectures.

## References and status check

- A. P. Austin and L. N. Trefethen, *Trigonometric interpolation and quadrature in perturbed points*, SIAM Journal on Numerical Analysis 55(5) (2017), 2113–2122. [DOI](https://doi.org/10.1137/16M1107760); [author PDF](https://people.maths.ox.ac.uk/trefethen/perturbed.pdf). The conjectured sharpening of (12) is stated on pp.2115–2116; the second-norm conjecture is on p.2119.
- A. P. Austin, *Some New Results on and Applications of Interpolation in Numerical Computation*, D.Phil. thesis, University of Oxford, 2016. [Author PDF](https://personal.math.vt.edu/apaustin/pubs/DPhilThesis.pdf). Chapter 3, Conjectures 3.5 (p.75) and 3.10 (p.82), supplies the original norm definitions and uniformity. The thesis's endpoint claim is not imported; the later 2017 paper's supercritical interval is followed.
- L. Chen, R. Lin and H. Zhang, *The smallest singular value of nonuniform Fourier matrices*, [arXiv:2608.21960v1](https://arxiv.org/abs/2608.21960v1), 22 August 2026. [Full text](https://arxiv.org/html/2608.21960v1). Introduction, Theorems 1.4–1.5 and equations (1.6)–(1.7), explicitly connect the new bounds to the second conjecture.
- A. Yu and A. Townsend, *On the stability of unevenly spaced samples for interpolation and quadrature*, BIT Numerical Mathematics 63 (2023), article 23. [DOI](https://doi.org/10.1007/s10543-023-00965-z). Theorem 2.1 and §6.2 concern the subcritical and oversampled regimes.

On 2026-09-11, checked the 2017 author paper, Austin's full thesis, the current August 2026 arXiv paper, and targeted searches for Austin–Trefethen conjectures, perturbed-grid Lebesgue constants, and subsequent proofs/counterexamples. No proof of the first displayed bound or removal of the logarithm in the second was located. The August 2026 result also addresses a smoother-function quadrature convergence question; that different question is not counted here. This is a bounded check, and the preprint's proofs have not been independently verified.
