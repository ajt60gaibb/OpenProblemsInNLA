# AC-01 — Is the matrix multiplication exponent two?

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Rating rationale:** Extreme because closing the exponent gap is a longstanding central barrier in algebraic algorithms; broad importance follows from matrix multiplication’s role throughout NLA and computational complexity.  
**Topic:** arithmetic complexity of dense matrix multiplication  
**Last checked:** 2026-11-26  
**Status:** Lean verified  

## Negative resolution — 24 November 2026

The square matrix multiplication exponent over $`\mathbb C`$ is $`9/4`$.
Theorem 1.1 of OpenAI's [*The matrix multiplication exponent is nine
fourths*](https://github.com/openai/math/blob/92b516ef8e2abf66c3db7aa31438d3010bc7956f/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/paper.pdf)
supplies the matching lower bound. The October upper bound below was also
extended to every field by Alimzhan Amanov, Maxim van den Berg and Jeroen
Zuiddam in [*Multiplying matrices via polynomials*, §4.4](https://arxiv.org/html/2610.30054v1).
The exponent is an infimum. The upper bound gives
$`O_{\varepsilon}(n^{9/4+\varepsilon})`$ for every $`\varepsilon>0`$.

### Lean proof and verification evidence

The pinned release proves
`OAI.LinearAlgebra.MatrixExponent.omega_eq` for rational circuits and
`OAI.LinearAlgebra.SpectralBooks.square_exponent` for division-free formal
polynomial circuits, over every field. A program defined on all complex
inputs gives rational-function identities because $`\mathbb C`$ is infinite.
The rational-circuit lower bound therefore applies to the original program
model, and the division-free upper bound gives programs defined on all inputs.
[With-division theorem](https://github.com/openai/math/blob/92b516ef8e2abf66c3db7aa31438d3010bc7956f/lean/OAI/LinearAlgebra/MatrixExponent/FieldFormula.lean) ·
[Division-free theorem](https://github.com/openai/math/blob/92b516ef8e2abf66c3db7aa31438d3010bc7956f/lean/OAI/LinearAlgebra/SpectralBooks/ExactExponent.lean).

Carlos Toledo's independent verification record of 25 November 2026 reports
that Lean's kernel and nanoda accepted both bridges to independently written
with-division statements, `Bridge.DivisionA` and `Bridge.DivisionB`, with
transitive axioms limited to `propext`, `Classical.choice` and `Quot.sound`.
The audit used Lean 4.34.1, mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, and the release's
[dependency manifest](https://github.com/openai/math/blob/92b516ef8e2abf66c3db7aa31438d3010bc7956f/lean/lake-manifest.json).
This catalog reviewed the theorem correspondence and public verification
record. The kernel checks were run by the external audit.
[Audit, rows K0 and F2](https://carlostoledo.co/omega/) ·
[Archived configurations, proof exports and dated logs](https://doi.org/10.5281/zenodo.24537370).

To reproduce the release theorem and axiom checks from the pinned revision,
run the following from its `lean` directory. The audit archive also contains
the two division Comparator configurations.

```
lake exe cache get
lake build OAI.LinearAlgebra.SpectralBooks.ExactExponent
check_dir=$(mktemp -d)
cat >"$check_dir/MatrixExponentAxioms.lean" <<'EOF'
import OAI.LinearAlgebra.SpectralBooks.ExactExponent
#print axioms OAI.LinearAlgebra.MatrixExponent.omega_eq
#print axioms OAI.LinearAlgebra.SpectralBooks.square_exponent
EOF
lake env lean "$check_dir/MatrixExponentAxioms.lean"
```

## Problem statement

Over the field $`\mathbb C`$, let $`M(n)`$ be the minimum number of
scalar additions, subtractions, multiplications, and divisions in an arithmetic
straight-line program computing every entry of $`AB`$ for arbitrary
$`A,B\in\mathbb C^{n\times n}`$. Programs must be defined on their intended inputs.
Set $`\omega=\inf\{\tau:M(n)=O(n^\tau)\}`$. Is $`\omega=2`$? Equivalently, for every
$`\varepsilon>0`$, can these products be computed in $`O(n^{2+\varepsilon})`$
arithmetic operations? This asks about asymptotic arithmetic cost; it does not
assert an $`O(n^2)`$ algorithm or a floating-point stability guarantee.

## Why it matters

Matrix multiplication is a basic cost driver for dense NLA.

## References and status

M. Bläser, [*Fast Matrix Multiplication*](https://theoryofcomputing.org/articles/gs005/gs005.pdf),
Graduate Surveys 5 (2013), §§1, 5, provides the computational model. E. Dupont
et al., [*Improving the matrix multiplication exponent with modern optimization
and AlphaEvolve*](https://arxiv.org/abs/2608.16884) (2026), abstract and §1,
reports $`\omega<2.371177`$. The October 2026 manuscript below gives a
stronger upper bound. The earlier exponent-two claim is recorded with its
verification limits.

## Status check — 2026-09-10

Rechecked [Dupont et al., August 2026](https://arxiv.org/abs/2608.16884), and searched for exponent-two proofs and newer matrix-multiplication bounds. Its reported bound is still strictly above two, at 2.371177. No proof of exponent two or a strict lower bound above two was located. Faster finite-size identities and improved numerical optimizations of existing bounds do not decide the asymptotic equality.

## Reviewed research submission — 14 September 2026

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation. [Verified affiliation and submission record](../../references/holden-ac-2026-09-14/README.md).

Sections 4–8 prove the auxiliary bound $`\widetilde R(\mathrm{cw}_2)<3.876919161`$, also relevant to [AC-04](../AC-04/README.md). The Section 10 scalar-tree obstruction is not a tensor-rank lower bound. Neither result proves $`\omega=2`$.

[Report](../../references/holden-ac-2026-09-14/AC-01-submission.pdf) · [Independent AI-agent audit and limitations](../../references/holden-ac-2026-09-14/verification/review-ac01-ac02.md). AI assistance was disclosed. This submission received an informal AI-agent audit.

## Literature update — 2026-10-06

OpenAI, [*An Upper Bound of 9/4 for the Matrix Multiplication
Exponent*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Matrix-Multiplication-Nine-Fourths-October-2-2026/paper.pdf),
manuscript dated 2 October 2026, Theorem 1.1, reports that, for every
$`\varepsilon>0`$, complex $`n\times n`$ matrix multiplication uses
$`O_{\varepsilon}(n^{9/4+\varepsilon})`$ arithmetic operations, hence
$`\omega(\mathbb C)\le9/4=2.25`$. The
[theorem source](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Matrix-Multiplication-Nine-Fourths-October-2-2026/build/paper.tex)
and the release's [Lean scope note, “Scope”](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/107.md)
are pinned to revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The scope
note reports an unconditional formalization for finite division-free arithmetic
programs with arbitrary positive exponent slack, which fits the arithmetic
model in this entry. This update reviewed the statement and published scope;
it did not rerun Lean or independently audit the proof. The reported upper
bound improved the August bound. The November result supplied the matching
lower bound.

### Unvalidated exponent-two claim — 18 September 2026

Zhi-Wei Sun, [*Tensor Degenerations for Matrix
Multiplication*](https://chinaxiv.org/abs/202609.00167), ChinaXiv:202609.00167.
The original [Math-ChinaXiv index](https://math.chinaxiv.org/server/mathindex.htm?locale=en)
lists this title with date 18 September 2026. A
[reproduced author abstract](https://chinarxiv.org/items/chinaxiv-202609.00167)
claims that, for every positive integer $`n`$ and every field $`\mathbb K`$,
the border rank of the $`2^n\times2^n`$ multiplication tensor is at most
$`2^{2n+1}`$, and claims the consequence $`\omega(\mathbb K)=2`$.
If established over $`\mathbb C`$, this would settle the displayed target.
During this check the original abstract and PDF endpoints returned HTTP 403;
the proof was inaccessible. The inspected evidence consists of the original
title/date listing and the reproduced abstract. No independent validation was
located in that check. The claimed exponent two conflicts with the
subsequently verified lower bound above.
