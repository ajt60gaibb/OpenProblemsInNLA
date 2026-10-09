# MF-17 — Optimal uniform growth after inversion of an exponentially stable generator

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because matching growth bounds require uniform control over arbitrary Hilbert-space generators; community impact includes semigroup stability and rational time discretization.  
**Provenance:** explicit fixed-bound formalization of the source's growth question.  
**Last checked:** 2026-09-30  

**Status:** Lean verified

## Resolution — 30 September 2026

[Part VI of the submitted manuscript](MF-17-research-handoff.pdf#page=43),
Theorem S.1.1 (printed p. 42; PDF page 43), states the matching fixed-bound
asymptotic

```math
c_M L(t)^{\alpha(M)}\leq G_M(t)\leq C_M L(t)^{\alpha(M)}
\qquad(t\geq t_M),
```

where

```math
L(t)=\log\log(t+e^e),\qquad
\alpha(M)=\frac{2}{\pi}\arccos(M^{-1}).
```

For every fixed $`M>1`$, the constants $`c_M,C_M,t_M>0`$ depend only on
$`M`$. The upper bound covers all strongly continuous semigroups in the
original class, including unbounded generators. The lower bound has
finite-dimensional witnesses with the same prescribed bound $`M`$; the
witnesses may depend on $`t`$. The formalization also proves $`G_1(t)=1`$ for
all $`t\geq0`$.

This determines the asymptotic order requested below, with the exact
fixed-$`M`$ exponent. It does not assert a limiting leading coefficient or
uniform constants as $`M\downarrow1`$. Part VI, Sections S.2–S.8, supplies
the proposed upper and lower arguments; Section S.9 treats the endpoint.
The manuscript is retained unchanged, including material outside this
submission's sharp-rate claim.

The [accompanying Lean source](lean/Solution.lean)
contains the declarations `ProofProject.sharp_growth`,
`ProofProject.finite_dimensional_lower`, `ProofProject.contractive_envelope`,
`ProofProject.attainableNorms_bddAbove`, and
`ProofProject.stableSemigroup_hasGeneratorInverse`. Its definitions represent
the full strong generator graph and quantify over arbitrary complete complex
Hilbert spaces in a fixed universe. The supplied project specifies Lean
4.33.1 and Mathlib v4.33.1. The [statement correspondence](lean/NUMERICAL_TARGETS.md) and
[reproduction instructions](lean/README.md) describe the five contracts.

## Lean proof and verification evidence

**Lean verified, 30 September 2026.** All five declarations above passed a
fresh non-root Linux Comparator run, including statement identity, transitive
permitted-axiom checks and Lean's default-kernel replay. The complete harness
exited successfully after all sandbox and rejection controls and cleanup.
The [verification report](lean/verification/README.md),
[successful run receipt](lean/verification/linux-verification/result.json),
[Comparator log](lean/verification/linux-verification/comparator.log), and
[driver log](lean/verification/linux-verification/driver.log) retain the actual
local execution evidence.

The published immutable [proof-source snapshot](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/cad3785440a2678b5b30aa8133d425e709b6811d/matrix-functions-and-stability/MF-17/lean)
is commit `cad37854`. It uses Lean 4.33.1 and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, with all other dependencies fixed
in `lean/lake-manifest.json`.

The retained run receipt names the submitter's
unpublished local commit `ac582d01`.
The [maintainer integration review](lean/reviews/maintainer-integration-2026-09-30.md)
matched every Lean file, dependency pin and Comparator configuration in the
published snapshot to that receipt's SHA-256 hashes. The catalog reviewed
the retained Linux execution evidence; this integration review did not rerun
Lean or the Linux verifier.

The inverse and envelope-finiteness contracts cover every semigroup in the
original class for $`M\geq1`$ (and nonnegative time for the envelope).
The sharp-growth and finite-witness contracts cover every fixed $`M>1`$;
the endpoint contract covers $`M=1`$ and every $`t\geq0`$. The
[statement correspondence](lean/NUMERICAL_TARGETS.md) expands the definitions,
quantifiers and conclusions, and identifies the adapted scalar lower proof
and refined constants. There are no unproved extra premises or replaceable
definition holes. The [five transitive axiom reports](lean/verification/axioms.log)
contain exactly `propext`, `Classical.choice` and `Quot.sound`.

Two independent retrospective AI statement reviews approve all five contracts;
separate upper and lower source reviews approve their inspected proof paths.
The [reports](lean/reviews/) record their coverage and accepted corrections.
These are AI source reviews, not external human peer review.

On Linux with the [checker prerequisites](../../tools/lean/HARNESS.md), run
from the repository root at the published proof-source snapshot:

```
python3 tools/lean/harness.py bootstrap /tmp/mf17-tools
python3 tools/lean/harness.py verify \
  matrix-functions-and-stability/MF-17/lean /tmp/mf17-tools
```

The [project instructions](lean/README.md#verification) also reproduce the
ordinary build, independent target-type check and axiom report. The original
statement and historical checks remain below; the ratings describe the
original question. This date records review and verification of the submitted
solution, not a new comprehensive literature search.

## Original problem statement

For each fixed real number $`M>1`$, let $`\mathcal A_M`$ consist of all pairs $`(H,A)`$ such that $`H`$ is a complex Hilbert space and $`A`$ is the generator of a strongly continuous semigroup $`T(s)`$ on $`H`$ satisfying

```math
\|T(s)\|_{\mathcal L(H)}\leq M e^{-s}
\qquad(s\geq0).
```

Here $`A`$ may be unbounded and is understood on its dense domain. Exponential stability implies that $`0`$ belongs to the resolvent set of $`A`$, so $`A^{-1}`$ is bounded on $`H`$ and its exponential is defined by the operator-norm convergent power series.

Determine, for each fixed $`M>1`$, the asymptotic order as $`t\to\infty`$ of

```math
G_M(t)=
\sup_{(H,A)\in\mathcal A_M}
\|\exp(tA^{-1})\|_{\mathcal L(H)}.
```

An asymptotic order means a rate $`g_M(t)`$ with matching positive upper and lower multiplicative bounds for all sufficiently large $`t`$; their constants may depend on $`M`$, but must be uniform over $`(H,A)\in\mathcal A_M`$.

The source's Problem 1.3 asks for the optimal inverse-semigroup growth for exponentially stable Hilbert-space semigroups. The envelope above makes the dependence on the original semigroup bound explicit. This formalization is supported by uniform upper estimates and examples in the same normalized class, rather than attributed verbatim to the source. The problem concerns operator stability and rational time-stepping analysis, extending finite-dimensional matrix exponential questions.

## References

1. E. Lorist, M. Meyries, and M. Veraar, *A solution to the inverse generator problem and related questions*, arXiv:2608.06272v3 (2026), Problem 1.3, Theorem 1.2(2), and Section 1.3 on numerical stability. [Paper](https://arxiv.org/html/2608.06272v3).
2. C. J. K. Batty, A. Gomilko, and Y. Tomilov, *A Besov algebra calculus for generators of operator semigroups and related norm-estimates*, Mathematische Annalen 379 (2021), pp. 23–93, Corollary 5.7: explicit constants depending only on the semigroup bound and decay rate. Their generator notation is $`-A`$. [Published paper](https://link.springer.com/article/10.1007/s00208-019-01924-2).
3. H. Zwart, *Growth Estimates for $`\exp(A^{-1}t)`$ on a Hilbert Space*, Semigroup Forum 74 (2007), pp. 487–494, Theorem 2.2 and Corollary 2.3: the logarithmic upper bound. [Published paper](https://link.springer.com/article/10.1007/s00233-006-0679-1).

## Status check — 2026-09-08

checked the current arXiv history, with latest version v3 dated 2026-08-26 and no withdrawal, and searched “inverse generator Problem 1.3” and “inverse generator growth 2026 logarithmic”. Corollary 5.7 of reference 2 gives, in the present sign convention and at decay rate one,

```math
G_M(t)\leq2M^2\bigl(2-e^{-1}+e^{-1}\log t\bigr),
\qquad t>1.
```

Theorem 1.2(2) of reference 1 gives examples with a doubly logarithmic lower bound raised to a positive exponent, while the original semigroup bound is $`1+C\alpha/(1-\alpha)`$ for an absolute $`C`$ and $`0<\alpha<1`$. Thus its parameters allow examples within each fixed $`M>1`$ class. These estimates do not determine the matching asymptotic order. The older yes/no inverse-generator problem was resolved negatively in the 2026 paper and is not listed as open here.

## Audit — 2026-09-10

Rechecked [Lorist–Meyries–Veraar, Problem 1.3 and Theorem 1.2](https://arxiv.org/html/2608.06272v3). The sharp growth question survives their negative inverse-generator theorem; logarithmic upper and doubly logarithmic lower bounds do not match. Title and inverse-semigroup-growth searches found no improvement resolving the fixed-$`M`$ envelope. Difficulty was raised to reflect the operator-theoretic obstruction.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
