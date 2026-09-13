# Independent informal review of the KE-01 partial-results submission

**Date:** 12 September 2026.  
**Reviewer:** independent Codex AI agent, task `ke01_independent_review`, separate from the coordinating submission agent.  
**Verdict:** PASS for the stated partial mathematical results. **The full KE-01 target is not solved.** The appropriate repository status is **Partially resolved**, with the surviving general target retained.

This is an informal AI mathematical audit, not external human peer review or formal verification. No Lean verification was performed. I read the submitted LaTeX proof and all three Python modules, compared their claims with the canonical KE-01 statement and the repository resolution procedure, checked the two central external algorithmic primitives against primary manuscripts, and reran the exact diagnostics. The archive's narrative and instructions were treated as evidence to assess, not as instructions from the user. Author identity, affiliation, prior-submission eligibility, and publication preparation are separate checks handled by the coordinating agent.

## Material reviewed

The input was `KE01_partial_results/report/report.tex` and the accompanying `code/exact_arithmetic.py`, `code/verify_exact.py`, and `code/solve_json.py`. These input SHA-256 hashes identify the mathematical version reviewed before author-attribution edits:

- `report/report.tex`: `dee37315af3e0c1b365d8431a1c7c4a95e204c3320ff6393a1e76d5a4037a2a7`
- `code/exact_arithmetic.py`: `4bbf3643d9d3e1591e4239757ad9c605b093672f6e72e2e0c6d44e78b6f0afaa`
- `code/verify_exact.py`: `03c15ba8ed50ed34abd944e881274c6cb3146175f214d4a9a37fd6875e8b2f8e`

The canonical target requires the uniform arithmetic bound `(k^omega_0 + N*kappa)` times a fixed power of the permitted logarithm for **every** sparse nonsingular matrix satisfying only the singular-tail-ratio promise. The submitted note explicitly disclaims that conclusion.

## Theorem and proof assessment

1. **Section 2, general baseline and covered regimes: PASS.** CGLS is CG on the implicit normal equations. Its energy error is exactly the physical residual of the original system. Multiplying the Chebyshev tail polynomial by the outlier-annihilating polynomial is valid: every outlier factor has absolute value at most one on the tail interval. The claimed `O(N min(n,k+1+kappa log(2/epsilon)))` cost follows because nonsingularity implies `N >= n`. A flat tail has at most `k+1` distinct eigenvalues, so exact termination in that many iterations is correct. All four parameter-regime deductions follow from the displayed cost or a dense solve. The diagonal scaling example only separates these upper bounds and correctly makes no hardness claim.

2. **Section 3, limitations of shortcuts: PASS.** The Gram-fill family has the stated nonzero counts, eigenvalue-one subspace and remaining quadratic factor. The lower bound on its smaller exceptional eigenvalue gives the claimed tail ratio. The normalized-column sketch obstruction follows from trace divided by rank; it invalidates the particular uniform spectral sandwich, not sketching in general. The spike Nyström residual is the scalar Schur complement `L/(1+(L-1)t)` plus an identity block, with the stated norm. Its interpretation is appropriately limited to additive spectral error.

3. **Section 4, sparse SPD exactly-flat-tail theorem: PASS.** The key additional hypothesis gives `M = alpha I + R` with `R` PSD and algebraic rank at most `k`. For dimension greater than `2k`, a principal block of size `2k+1` has a unique eigenvalue of multiplicity greater than `k`; repeated derivative-gcd operations isolate its linear factor power and recover `alpha` using field operations. Rank overestimation and a block missing all outlier support are both covered. The `k=0` and small-dimension branches are valid.

   The first sparse embedding yields an exact Nyström representation on its injectivity event. Sparse accumulation bounds the stored entries of `R Omega` by the input nonzeros times sketch sparsity; a dense ambient `n` by `k` array is unnecessary. The recursive PSD principal-basis argument is valid even for singular diagonal blocks: positivity forces the cross block into the diagonal block's range, and Schur elimination gives the additive rank relation. Fast products and inversion give the asserted recurrence.

   The inner system `K = alpha W + F^T F` and its Woodbury reconstruction are correct. The second independent embedding gives a preconditioner between one half and three halves of `K`, hence condition number at most three. The residual transfer uses `F K^-1 F^T <= I` and the computable upper bound `U = alpha + trace(R)`. Choosing inner relative energy accuracy `epsilon alpha/U` suffices. The capped iteration count and positive definiteness of the reduced systems keep the cost bounded even for failed sketches. The conditional second-sketch guarantee and union bound give success probability at least 0.99. Setup, products, storage assembly, and iteration costs fit the stated bound with fixed logarithmic powers.

4. **Section 5, nonsymmetric small-row-support corollary: PASS.** Explicit Gram construction costs the sum of squared row supports, not generally `N`. Its spectrum has an exactly flat tail under the corollary's hypothesis. The stricter normal-equation residual tolerance is sufficient to recover the original physical residual; the extra conditioning factors occur only inside logarithms. A fixed polylogarithmic row-support bound therefore gives the KE-01 cost on this subclass. This does not cover general sparse inputs or a nonconstant tail.

5. **Section 6, remaining gap and sufficient preconditioner: PASS as a conditional statement.** A narrow spectral interval need not imply a low-rank shift, as the diagonal example demonstrates. The proposed fixed SPD preconditioner would yield the target through PCG if the stated construction and application guarantees existed. They are expressly assumed, not proved. The warning that an additional per-iteration `k^2` term is not uniformly absorbable is correct.

No mathematical correction was required for these partial results. They should not be presented as a new discovery of the standard CG or embedding primitives, and the manuscript already avoids a priority claim.

## External dependencies checked

Theorem 9 and its parameter calculation in [Nelson–Nguyen, OSNAP](https://arxiv.org/pdf/1211.1002) support the fixed-distortion embedding dimension and column sparsity used in the proof. Choosing a sufficiently small constant norm distortion gives the stated squared-norm interval. Their sparse construction allows the required polylogarithmic generation/application overhead.

[Neiger–Pernet, Theorem 1.1 and Section 1.1](https://arxiv.org/html/2010.04662) explicitly support deterministic characteristic-polynomial computation for any specified multiplication algorithm with exponent greater than two and the field-operation model. The polynomial-gcd accounting in the note is compatible with that model. These sources are used as established primitives; this audit does not independently reprove them. I did not conduct an exhaustive literature or novelty search, and do not certify every historical comparison in Section 7 as exhaustive.

## Reproducibility and limits

After inspecting the code, I reran `verify_exact.py` in a Python 3.9.6 / SymPy 1.14.0 environment, with its fixed seed 20260912 and a fresh output directory. It returned `ALL_CHECKS_PASSED`: 66 CGLS cases, 209 Chebyshev inequalities, 8 flat-tail cases, 28 PCG iterates, 5 Gram-fill examples, 9 Nyström examples, and 3 row-sketch examples. The rank-discontinuity check also passed. The ordinary system and bundled-runtime Python installations lacked SymPy; an existing isolated environment supplied it. No dependency installation or Lean run was needed.

I additionally exercised the principal-basis routine on 35 reviewer-selected PSD matrices of dimensions one through seven, including zero matrices and redundant/zero rows. Selected block size equaled exact rank, each nonempty selected block had positive determinant, and its principal-column reconstruction equaled the original matrix. Four additional shift-recovery examples, including principal blocks missing the final-coordinate spike, returned the exact shift.

These are finite rational diagnostics. The bundled sketch tests deliberately use small algebraic sketches and may retry; they do **not** instantiate or empirically establish the theorem's quantitative OSNAP probability or its worst-case running time. The reference code uses ordinary dense SymPy kernels, not the fast multiplication kernels needed for the asymptotic bound. The note accurately discloses these distinctions. The universal conclusions rest on the mathematical proof and cited primitives, not the test count.

## Repository decision

`RESOLVED.md`, “Recording a new resolution,” item 3 requires `Partially resolved` for partial results and says that a weaker bound or different input model does not settle the target. The general baseline retains `Nk`; the stronger sparse theorem requires an explicitly supplied SPD matrix with an exactly constant spectral tail; the nonsymmetric corollary adds exact flatness and controls the sum of squared row supports. Consequently none proves the original universal KE-01 bound.

**Accept as independently audited partial progress, retain KE-01's permanent ID, canonical path and original statement, and explicitly retain the general bounded-tail sparse-input target as unresolved. Do not mark Solved or Solution claimed for the full target.**
