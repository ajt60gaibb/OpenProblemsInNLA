# IE-08 — A cubic-time Schur algorithm using logarithmic precision

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** Lean verified  
**Last checked:** 2026-11-24  

**Rating rationale:** Extreme reflects an end-to-end precision and complexity theorem for general Schur decomposition; broad impact is justified by this central eigenvalue-computation task.

## Stronger resolution and Lean verification — 2026-11-24

**Affirmative resolution by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Theorem 1** of [*Schur decomposition with logarithmic precision in cubic time up to logarithmic factors*](https://arxiv.org/abs/2611.29923) gives the stronger bound

```math
O(n^3\log^2(n/(\delta p)))\quad\text{arithmetic operations and}\quad
O(\log(n/(\delta p)))\quad\text{mantissa bits},
```

for every requested failure probability $`0< p<1/2`$. It returns an exactly upper triangular $`T`$ on every execution, and both original residual bounds hold jointly with probability at least $`1-p`$. The work bound holds on every execution. Taking $`p=0.01`$ settles the original target with $`c=2`$, without any separation or diagonalizability assumption. The original ID, statement, September resolution and historical ratings are retained.

The complete main theorem is registered as [Palomar PALOMAR-2026-11-23-000003, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-11-23-000003&version=1). The evidence below supports **Lean verified** for the full target.

## Lean proof and verification evidence

The [proof source](https://github.com/MColbrook/logarithmic-precision-schur/tree/6035fb72968d7a5d4cf8e86c92aa3c49d330f9a7) is pinned to `6035fb72968d7a5d4cf8e86c92aa3c49d330f9a7`. Its [toolchain](https://github.com/MColbrook/logarithmic-precision-schur/blob/6035fb72968d7a5d4cf8e86c92aa3c49d330f9a7/lean-toolchain) is Lean `v4.35.0-rc3`; [lake-manifest.json](https://github.com/MColbrook/logarithmic-precision-schur/blob/6035fb72968d7a5d4cf8e86c92aa3c49d330f9a7/lake-manifest.json) pins mathlib to `c55e6e786f49471c72fbddbec5415808896aec1e` and records every other dependency revision.

**Statement correspondence.** [Solution.lean](https://github.com/MColbrook/logarithmic-precision-schur/blob/6035fb72968d7a5d4cf8e86c92aa3c49d330f9a7/Solution.lean) proves `SchurFormal.main_result : SchurFormal.MainTheorem`. The [model and definitions](https://github.com/MColbrook/logarithmic-precision-schur/blob/6035fb72968d7a5d4cf8e86c92aa3c49d330f9a7/Schur/Model.lean) quantify one finite program and a positive universal constant before every positive dimension, complex contraction and admissible tolerance and confidence request. `spectralNorm` is the induced Euclidean norm; `GoodOutput` is the conjunction of the two original residual inequalities for the exact stored matrices. `RunWithinBounds` gives every-execution termination, precision and work bounds and exact triangularity. `RequestCoverage` proves that every allowed real request has a valid dyadic control encoding; no additional input promise or unproved algorithmic premise is required. Fixing $`p=0.01`$ gives precisely the original confidence requirement. See the [statement-fidelity review](https://github.com/MColbrook/logarithmic-precision-schur/blob/6035fb72968d7a5d4cf8e86c92aa3c49d330f9a7/reviews/main-theorem-fidelity.md).

**Successful public verification.** Palomar verified this revision on **23 November 2026**, in [run 45082158221](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/45082158221). Its immutable [mechanical report](https://data.palomar-registry.org/evidence/PALOMAR-2026-11-23-000003-v1/dbc0fc5d5255ef85750629e81bcfc31df7d60e0f6c95f314df9044f1720275bc/mechanical-report.json) records full build and Comparator success, including NanoDa and Lean default-kernel acceptance against the independently stated Challenge. The [automated review](https://data.palomar-registry.org/evidence/PALOMAR-2026-11-23-000003-v1/dbc0fc5d5255ef85750629e81bcfc31df7d60e0f6c95f314df9044f1720275bc/review.json) found no material statement mismatch and recorded no requested changes. This catalog reviewed those public records and the pinned statement; it did not rerun Lean locally.

**Transitive axioms.** The pinned [axiom log](https://github.com/MColbrook/logarithmic-precision-schur/blob/6035fb72968d7a5d4cf8e86c92aa3c49d330f9a7/verification/main-solution-lean.log) reports `SchurFormal.main_result` depending exactly on `propext`, `Classical.choice` and `Quot.sound`. There is no `sorryAx`, custom axiom or additional native-execution trust in the target proof. The deliberate statement hole in Challenge is outside Solution's proof dependencies.

**Reproduction.** With the pinned Lean toolchain, Git, Python 3.10 or later and bubblewrap on Linux:

```
git clone \
  https://github.com/MColbrook/logarithmic-precision-schur.git
cd logarithmic-precision-schur
git checkout 6035fb72968d7a5d4cf8e86c92aa3c49d330f9a7
python3 scripts/check-package.py \
  --output verification/package-check.json
lake exe cache get
lake build
bash scripts/check-main.sh
```

The [verification index](https://github.com/MColbrook/logarithmic-precision-schur/blob/6035fb72968d7a5d4cf8e86c92aa3c49d330f9a7/verification/README.md) explains the logs. The proof uses unrestricted binary exponents and rounding half ties upward, within the target's relative-error model. It formalizes the complete main theorem, with a weaker intermediate Gaussian constant, rather than every intermediate estimate or the experimental software. The source and reviews disclose AI assistance; the automated reviews do not constitute external human peer review.

## Earlier resolution — 2026-09-11

**Affirmative resolution by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. [Complete manuscript](solution.md) · [PDF](solution.pdf) · [LaTeX](solution.tex). **Theorem 1, Lemmas 2–12 and the final four proof sections.**

The end-to-end algorithm uses $`O(n^3\log^c(n/\delta))`$ arithmetic operations and $`O(\log(n/\delta))`$ mantissa bits, with universal constants, for every complex input with $`\|A\|_2\le1`$. With probability at least $`0.99`$ it returns an exactly upper triangular $`T`$ and a $`Q`$ satisfying both displayed residual bounds. The proof includes finite random sampling, deterministic work caps, global recursive conditioning and floating-point error control, without an input separation or diagonalizability assumption. It is an asymptotic existence result with conservative constants, not a production implementation.

The complete argument received an independent Codex-agent **PASS** on 11 September 2026. The [review report](../../references/colbrook-additional-2026-09-11/verification/reviews/IE-08-review.md) records the exact scope and a hash of the original reviewed manuscript. The mathematical sections remain unchanged in the authored version. Original ChatGPT generation is disclosed; that September submission asserted neither external human peer review nor a formal proof certificate. [Submission and verification record](../../references/colbrook-additional-2026-09-11/README.md).

The original statement, source references and prior audit notes are retained; the former difficulty rating is historical.

## Problem statement

Does a randomized floating-point algorithm exist with the following guarantee? Given $`A\in\mathbb C^{n\times n}`$, $`\|A\|_2\leq1`$, and $`0<\delta<1/2`$, it uses at most

```math
O(n^3\log^c(n/\delta))\quad\text{arithmetic operations and}\quad
O(\log(n/\delta))\quad\text{mantissa bits}
```

and, with probability at least $`0.99`$, returns an upper triangular $`T`$ and $`Q`$ satisfying

```math
\|A-QTQ^*\|_2\leq\delta,
\qquad \|Q^*Q-I\|_2\leq\delta?
```

The constants and exponent $`c`$ must be universal, with no additional eigenvalue-separation or diagonalizability assumption. Use the usual relative-error floating-point model, with sufficient exponent range to avoid overflow and underflow. This is a statement about the precision needed for a rigorous algorithm, not whether ordinary QR implementations usually work well.

## References

Amsel et al., [*Linear Systems and Eigenvalue Problems*](https://arxiv.org/html/2602.05394v3#S3.SS2), Problem 3.3. Schneider, [*Pseudospectral Divide-and-Conquer for the Generalized Eigenvalue Problem*](https://escholarship.org/content/qt3bb8s95w/qt3bb8s95w_noSplash_22c8cf7d2873d111b5bb367d09dc40fc.pdf), dissertation, §1.6.1 and Chapter 6. Banks et al., [FOCM diagonalization paper](https://doi.org/10.1007/s10208-022-09577-5), §6, precision-reduction question.

## Earlier status check — 2026-09-08

Searches for `Schur logarithmic precision 2026` and `site:arxiv.org Schur precision 2026` found no complete analysis meeting both bounds. The dissertation explicitly distinguishes analyzed subroutines from an end-to-end precision theorem.

## Audit update — 2026-09-10

Rechecked [workshop version 3](https://arxiv.org/html/2602.05394v3), Problem 3.3 and its update. The report still distinguishes algorithmic ingredients from a complete logarithmic-precision analysis. Targeted cubic-Schur and precision searches found no theorem meeting every displayed requirement.
