# IE-18 — The exact four-step amplification of restarted Anderson acceleration

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Lean verified
**Last checked:** 2026-09-12

<!-- colbrook-recovered -->
## Independently reviewed resolution - 2026-09-11

**Negative resolution.** Section 2 refutes the exact four-step identity using $`M=\mathop{\mathrm{diag}}\nolimits(1/10,1/2,3/5)`$ and $`v=(1,1,1)^T`$: the squared norm ratio is $`1920682/21289638243>1/14641`$, the square of the proposed factor. Both $`M`$ and $`I-M`$ are positive definite. Section 3 proves unbounded underestimation over a parameter family. The separate asymptotic convergence question is not resolved.

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. [Complete manuscript](../../references/colbrook-recovered-2026-09-11/manuscripts/IE-18.pdf), [independent proof review](../../references/colbrook-recovered-2026-09-11/verification/reviews/IE-18-review.md), and [submission record](../../references/colbrook-recovered-2026-09-11/README.md). The supplied notes were reconstructed with substantial AI assistance. This is independent agent verification, not external human peer review or formal proof-assistant certification; no novelty or priority claim is made.

The difficulty, importance and rating rationale below are historical assessments of the original open target. Original statements, references and dated audits are preserved.

The complete negative answer to the original identity now has [Lean proof and verification evidence](#lean-proof-and-verification-evidence--2026-09-12). The stronger parameter-family result and separate asymptotic question are outside that formalization.
<!-- /colbrook-recovered -->

**Rating rationale:** Challenging reflects a global maximization of a nonlinear homogeneous residual map in arbitrary dimension; community impact is an exact convergence factor for restarted Anderson acceleration.

Let $`n\ge2`$ and let $`M\in\mathbb R^{n\times n}`$ be nonzero and symmetric, with $`1\notin\sigma(M)`$. Put $`A=I-M`$. Define the positively homogeneous map

```math
R(v)=M\left(v-\frac{v^TAv}{\|Av\|_2^2}Av\right)\quad(v\ne0),\qquad R(0)=0.
```

Two steps of restarted Anderson acceleration with memory one applied to $`x=Mx+b`$ propagate the residual by $`R`$. If $`m_1,\ldots,m_n`$ are the eigenvalues of $`M`$, is

```math
\max_{v\ne0}\frac{\|R(R(v))\|_2}{\|v\|_2}
=
\max_{i\ne j}
\left(\frac{m_im_j(m_j-m_i)}{|m_i(m_i-1)|+|m_j(m_j-1)|}\right)^2?
```

A term with zero denominator is defined as zero: under the assumptions this can occur only when $`m_i=m_j=0`$.

The conjecture says that a largest four-step residual amplification is attained using only two orthogonal eigenvectors, irrespective of the dimension. It supplies an exact worst-case factor for this restart scheme, relevant to accelerated stationary solvers and multigrid.

## References

 O. A. Krzysik, H. De Sterck, and A. Smith, *Asymptotic convergence of restarted Anderson acceleration for certain normal linear systems*, SISC 47(2025), Conjecture 10, (9),(16),(24),(27) ([journal](https://doi.org/10.1137/24M1672262); [arXiv v4](https://arxiv.org/html/2312.04776v4)). Conjecture 10 states the maximum through two-eigenvector nonlinear eigenvalues; equation(24) evaluates their scalar maximum. The map formulation above also covers exact termination without an undefined $`\alpha(0)`$.

## Status check — 2026-09-08

 The arXiv history lists v4,12 May 2025, as latest. Its Conjecture 10 and journal abstract retain the conditional result. Searches for the paper title, “restarted Anderson Conjecture 10”, and later proof/counterexample results found no resolution. Windowed AA, GMRES(1), and restarted CG use different residual maps. The September 2026 Forsythe paper resolves the CG restart question and is not a solution claim for the map above.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

## Audit update — 2026-09-10

Rechecked [version 4](https://arxiv.org/html/2312.04776v4), Conjecture 10 and its surrounding discussion, against the [2025 journal record](https://doi.org/10.1137/24M1672262). The general-dimensional identity is still conjectural; the order-two case alone does not justify a substantive partial-status label. Targeted searches for this four-step amplification conjecture found no later resolution.

## Lean proof and verification evidence — 2026-09-12

**Mathematical counterexample:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Lean formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance.

The [immutable proof revision](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/7b8512e21c50adc8597dcdbed32f2aec13c3b43e/linear-systems-and-elimination/IE-18/lean) contains the actual residual, Euclidean norm, spectrum and eigenvalue-maximum definitions. [Solution.lean](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/7b8512e21c50adc8597dcdbed32f2aec13c3b43e/linear-systems-and-elimination/IE-18/lean/Solution.lean) exports:

- `NLA.IE18.residual_certificate`: both actual residual-map evaluations, nonzero denominators, coefficients and exact squared norm ratio.
- `NLA.IE18.counterexample`: the admissible positive definite witness, actual spectral maximum and strict violation of the claimed greatest amplification.
- `NLA.IE18.not_fourStepConjecture`: negation of the full original universal identity, for all dimensions at least two and all nonzero real symmetric matrices with one excluded from the spectrum.

All witness hypotheses are proved. The maximum uses the actual eigenvalues with multiplicity and distinct indices; the residual map and zero convention are preserved. The squared-ratio comparison with $`(1/121)^2`$ implies the strict unsquared violation. The stronger parameter family and separate asymptotic question are outside the formalized claims.

The toolchain is Lean **4.33.1**, with [LeanCert at `621a43d7cf21`](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926), [Mathlib at `0df444a360ea`](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474), and [all dependency revisions locked](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/7b8512e21c50adc8597dcdbed32f2aec13c3b43e/linear-systems-and-elimination/IE-18/lean/lake-manifest.json). LeanCert certifies one exact rational comparison in kernel mode. All eight audited internal/public declarations have only `propext`, `Classical.choice`, and `Quot.sound` in their transitive axiom closure.

The catalog reviewed the [successful Ubuntu Linux run](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34703657954): fresh project builds, sandbox/rejection controls, exact Challenge/Solution matching and default-kernel replay passed for all exports. The official Mathlib compiled cache was used. [The audit, original artifact and raw logs](lean/verification/linux-2026-09-12/), [independent statement and proof reviews](lean/reviews/), and [formalization metadata](lean/formalization.yaml) are retained. These are AI-agent reviews of remote Linux verification, distinct from local Mac builds or human peer review.

[Reproduction commands](lean/README.md#reproduction-and-evidence) use the immutable proof revision and the [shared harness](../../tools/lean/HARNESS.md) on a non-root Linux host.
