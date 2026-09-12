# MI-29 — Modulus-order determinant comparison with an arbitrary base power

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Lean verified
**Last checked:** 2026-09-12

**Rating rationale:** Arbitrary base powers and indefinite Hermitian factors make extension of the squared-base theorem challenging; the comparison has specialist importance for determinant inequalities.

## Resolution — 2026-09-11

**Negative result by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent proof review: PASS.**

A rational positive definite $`A`$ and invertible indefinite Hermitian $`B`$ in dimension three, with $`k=6`$ and $`p=8`$, reverse the proposed determinant comparison. The exact right-minus-left gap is $`21036678407451/156250000000000>0`$. The known $`k=2`$ theorem and the variant $`B>0`$ are not contradicted.

The exact target is resolved. The complete negative answer now has [Lean proof and verification evidence](#lean-proof-and-verification-evidence--2026-09-12). The original statement and source evidence are retained below; its former difficulty rating is historical.

**Primary manuscript:** [complete proof PDF](solution.pdf), [standalone TeX](solution.tex), Theorem 1.1 and its proof; [authorship and scope](solution.md). The [independent review](../../references/colbrook-matrix-2026-09-11/verification/reviews/MI-29-review.md) checks the full original argument and records its hash. The draft was AI-assisted; the 2026-09-11 review was independent agent verification, without external human peer review or formal certification. The later Lean verification below covers the complete negative answer. [Submission record](../../references/colbrook-matrix-2026-09-11/README.md).

## Lean proof and verification evidence — 2026-09-12

**Mathematical counterexample:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Lean formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance.

The [proof at revision c0c5ece](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/c0c5eced77d2528f37d931200248fc54a190813e/matrix-inequalities-and-norms/MI-29/lean) establishes the complete negative answer with the actual continuous functional calculus and matrix modulus. Its exact admissible dimension-three witness at $`k=6,p=8`$ has right-minus-left determinant gap $`21036678407451/156250000000000>0`$. The final negation retains every positive dimension, every complex positive definite $`A`$, every invertible Hermitian $`B`$, and all nonnegative real exponents. Every witness hypothesis is proved; positivity or commutation of $`B`$ is not added.

[Solution.lean](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/c0c5eced77d2528f37d931200248fc54a190813e/matrix-inequalities-and-norms/MI-29/lean/Solution.lean) exports:

- `NLA.MI29.spectralPower_natCast`: actual spectral powers agree with matrix natural powers, including exponent zero.
- `NLA.MI29.modulus_power_eight`: the genuine square-root modulus, its positivity and the eighth-power reduction.
- `NLA.MI29.comparison_positive_real`: both determinants are positive real numbers under the original hypotheses.
- `NLA.MI29.counterexample`: the full admissible witness, analytic reductions, exact determinants and strict violation.
- `NLA.MI29.not_modulusDeterminantConjecture`: negation of the complete original conjecture.

Two independent agents [reviewed the frozen statements and complete proof](lean/reviews/) against the original target. [Linux run 34706412510](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34706412510) executed the actual sandboxed Comparator on GitHub Actions Ubuntu 24.04, matched all five declarations and replayed the solution through Lean's default kernel. The [archived logs and independent operational audit](lean/verification/linux-2026-09-12/) retain the immutable source hashes, original artifact digests and successful sandbox, raw-kernel and axiom-rejection controls. The [transitive axiom report](lean/reviews/proof-axioms.log) contains only `propext`, `Classical.choice` and `Quot.sound`. This catalog reviewed the remote Linux execution; local macOS proof reviews are recorded separately. These are independent AI-agent reviews, not external human peer review or source-author endorsement. Comparator checks formal identity and kernel trust; the statement referees separately reviewed correspondence with the original prose.

The proof pins **Lean 4.33.1**, [LeanCert 621a43d](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926) and [Mathlib 0df444a](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474), with [all dependency revisions locked](lean/lake-manifest.json). Generic CFC identities reduce the calculation to repeated squaring and exact three-dimensional determinants; one kernel-mode LeanCert rational point certificate supplies the strict scalar gap. The [formalization manifest](lean/formalization.yaml), [numerical targets](lean/NUMERICAL_TARGETS.md) and [project guide](lean/README.md) record scope and reproduction. The source's separate singular-input extension, established $`k=2`$ result and positive-$`B`$ variants are outside these exports.

From a checkout of the verified proof revision, on an isolated non-root Linux host meeting the [shared harness prerequisites](../../tools/lean/HARNESS.md), run:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  matrix-inequalities-and-norms/MI-29/lean \
  /absolute/path/to/nla-lean-tools
```

## Problem statement

Does the inequality

```math
\det(A^k+|AB|^p)\ge\det(A^k+|BA|^p)
```

hold for every integer $`n\ge1`$, every positive definite $`A\in\mathbb C^{n\times n}`$, every invertible Hermitian $`B\in\mathbb C^{n\times n}`$, and every pair of real parameters $`k,p\ge0`$? Here $`|X|=(X^*X)^{1/2}`$, all powers of positive definite matrices use spectral functional calculus, and $`X^0=I`$.

Both determinants are positive real numbers. The same conjecture is stated for semidefinite $`A`$ and Hermitian $`B`$ in the source; invertible inputs avoid zeroth-power conventions, while the positive-exponent singular cases follow by continuous approximation. No commutation between $`A`$ and $`B`$ is assumed.

The two moduli have the same singular spectrum, but adding $`A^k`$ tests their alignment with the eigenvectors of the base matrix. The question therefore concerns how spectral data and eigenvector geometry interact in determinant estimates for matrix functions.

## References

1. M. M. Ghabries, *Contributions to Matrix Inequalities and Some Applications*, PhD thesis, University of Angers and Lebanese University (2022), §2.5 and final Open Problems, Problem 2, pp. 109–110. [Thesis uploaded by its author](https://www.researchgate.net/publication/361793582_Contributions_to_Matrix_Inequalities_and_Some_Applications).
2. M. M. Ghabries, H. Abbas and B. Mourad, *On some open questions concerning determinantal inequalities*, Linear Algebra Appl. 596 (2020), 169–183, resolution of the earlier $`k=2`$ question. [Publisher](https://doi.org/10.1016/j.laa.2020.03.009).
3. M. M. Ghabries, *A log-majorization inequality for normal matrices with applications to determinantal inequalities and geometric means*, arXiv:2607.21163v1 (2026), §3. [Full text](https://arxiv.org/html/2607.21163).

Status check (2026-09-10): the thesis states the full question after proving $`k=2`$ for all $`p\ge0`$, and further cases when both matrices are positive semidefinite. The July 2026 paper extends the known squared-base result to normal matrices, but does not claim arbitrary $`k`$ here. Searches for the exact titles, “modulus determinant arbitrary power conjecture Ghabries”, and 2025/2026 found no complete resolution. The negative-power companion in the thesis is not counted separately.
