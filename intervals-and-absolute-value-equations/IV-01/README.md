# IV-01 — Two-vertex certification of nonsingular sign regularity

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Lean verified

**Area:** structured matrices and interval linear algebra  
**Last checked:** 2026-10-15

**Rating rationale:** These ratings are historical and refer to the original question: extending two-vertex certification through zero minors in arbitrary dimension was challenging, with specialist impact in the efficient recognition of structured interval matrix families.

## Resolution — 15 October 2026

**Resolved affirmatively.** Wenqi Zhu (University of Oxford), Kai Zou
(King's College London), and Ping Nie (University of Waterloo).

The answer is **yes**. For every positive integer dimension, arbitrary real
entrywise bounds, and every common signature, nonsingular sign regularity at
the two checker vertices implies nonsingular sign regularity throughout the
closed matrix interval. The result allows arbitrary fixed entries, including
fixed zeros of both checker parities, and vanishing proper minors. The range
$`n\ge1`$ includes the original question's $`n\ge5`$, with no additional
hypothesis on the interval or its signature.

The primary formal result is
[`IV01.twoCheckerVertices`](https://github.com/erenup/two-vertex-sign-regularity/blob/22fedcfb6940fd943d67f1582068ed5b9b91a83e/lean/IV01/Statement.lean).
Theorem 1.1 of the [paper, *Two-vertex certification of nonsingular sign-regular
matrix intervals*](https://github.com/erenup/two-vertex-sign-regularity/blob/22fedcfb6940fd943d67f1582068ed5b9b91a83e/paper/main.pdf)
states the equivalent two-vertex characterization. The
[Lean proof and verification evidence](#lean-proof-and-verification-evidence)
below gives the exact statement comparison and reproducible formal record.
The retained partial-result and literature records below predate this resolution.

## Lean proof and verification evidence

### Immutable source and dependencies

The [proof repository at `22fedcfb6940fd943d67f1582068ed5b9b91a83e`](https://github.com/erenup/two-vertex-sign-regularity/tree/22fedcfb6940fd943d67f1582068ed5b9b91a83e)
pins Lean **`v4.34.0-rc2`** in its
[toolchain file](https://github.com/erenup/two-vertex-sign-regularity/blob/22fedcfb6940fd943d67f1582068ed5b9b91a83e/lean/lean-toolchain)
and Mathlib **`85e3a25e006c35636f0e53b0e9296caca2685bc0`** in its
[dependency manifest](https://github.com/erenup/two-vertex-sign-regularity/blob/22fedcfb6940fd943d67f1582068ed5b9b91a83e/lean/lake-manifest.json).
The manifest pins all remaining dependencies as well.

### Declarations and statement correspondence

All predicates used by the target are defined in
[`lean/IV01/Definitions.lean`](https://github.com/erenup/two-vertex-sign-regularity/blob/22fedcfb6940fd943d67f1582068ed5b9b91a83e/lean/IV01/Definitions.lean).
The [complete correspondence](https://github.com/erenup/two-vertex-sign-regularity/blob/22fedcfb6940fd943d67f1582068ed5b9b91a83e/LEAN_STATEMENT_CORRESPONDENCE.md)
compares them with the original catalogue statement:

- **Matrices and dimensions:** `Square n` is `Matrix (Fin n) (Fin n) Real`.
  The theorem quantifies over every $`n\ge1`$ and all real matrices of that
  dimension. This includes every $`n\ge5`$ in the original question.
- **Signature:** `IsSignature n ε` requires `ε k = 1` or `ε k = -1` for
  every $`1\le k\le n`$. The function `ε : Nat → Real` represents the finite
  signature by minor order. Unused values are unrestricted; every original
  signature extends to this representation.
- **Interval:** `EntrywiseLE L U` is the ordinary pointwise inequality, and
  `InBox L U M` means $`L\le M\le U`$. The interval is closed, with no
  strict-width condition. Fixed coordinates may occur anywhere.
- **Checker vertices:** `checkerMinus` chooses the lower entry at even
  row-plus-column parity and the upper entry at odd parity; `checkerPlus`
  reverses those choices. Lean's zero-based row and column labels preserve
  the original checker parity when both are shifted to one-based labels.
- **All minors and weak signs:** `SignRegular ε M` quantifies over every
  order $`1\le k\le n`$ and every pair of strictly increasing row and column
  maps. Its inequality is $`0\le\epsilon_k\det M[I,J]`$. These are all
  minors, with row and column indices in increasing order; proper zero
  minors are allowed.
- **Nonsingularity and common signature:** `NonsingularSignRegular ε M`
  is the conjunction of `Matrix.det M ≠ 0` and `SignRegular ε M`. Both
  checker-vertex assumptions and the conclusion use the same `ε`.
  Nonsingularity is assumed only at the two checker vertices and proved
  for every matrix in the box.

[`IV01.twoCheckerVertices`](https://github.com/erenup/two-vertex-sign-regularity/blob/22fedcfb6940fd943d67f1582068ed5b9b91a83e/lean/IV01/Statement.lean)
proves the complete original implication. Its premises are the dimension,
signature, entrywise bounds, the two endpoint conditions, and membership of
the arbitrary matrix in the box. Its rectangle-exclusion ingredients are
proved dependencies, not extra assumptions. There are no additional conditions on fixed coordinates, their directed
graph, or vanishing proper minors.

The supporting declarations
[`IV01.checkerMinus_mem_box` and `IV01.checkerPlus_mem_box`](https://github.com/erenup/two-vertex-sign-regularity/blob/22fedcfb6940fd943d67f1582068ed5b9b91a83e/lean/IV01/Box.lean)
prove that both checker vertices belong to the box. Specializing the universal
box property to them gives the converse in the paper's equivalence; the
catalogue question itself asks for the implication already proved by the
main target. No separate bundled equivalence declaration is claimed.

### Reproduction and verification record

The [verification record](https://github.com/erenup/two-vertex-sign-regularity/blob/22fedcfb6940fd943d67f1582068ed5b9b91a83e/VERIFICATION.md)
links the dated successful
[build log](https://github.com/erenup/two-vertex-sign-regularity/blob/22fedcfb6940fd943d67f1582068ed5b9b91a83e/lean/verification/2026-10-14-build.log),
[build receipt](https://github.com/erenup/two-vertex-sign-regularity/blob/22fedcfb6940fd943d67f1582068ed5b9b91a83e/lean/verification/2026-10-14-receipt.json),
and [dependency record](https://github.com/erenup/two-vertex-sign-regularity/blob/22fedcfb6940fd943d67f1582068ed5b9b91a83e/lean/verification/2026-10-14-dependencies.json).
On 14 October 2026, all 41 production modules were compiled into initially
empty project objects with the pinned compiler and dependency libraries.
**The catalogue did not rerun the checks**; the evidence supplied for this
status is the external project's verification record. The installed compiler
and pinned dependency libraries are disclosed trusted inputs; their original
builds were not reconstructed.

With the pinned Lean toolchain installed, reproduce from the immutable revision:

```
git clone https://github.com/erenup/two-vertex-sign-regularity.git
cd two-vertex-sign-regularity
git checkout --detach 22fedcfb6940fd943d67f1582068ed5b9b91a83e
cd lean
lake exe cache get
python3 -B verify.py --output .audit-build
```

The output directory must be new. The
[Lean guide](https://github.com/erenup/two-vertex-sign-regularity/blob/22fedcfb6940fd943d67f1582068ed5b9b91a83e/lean/README.md)
documents the compiler pin, dependencies, resource requirements and rejection
controls. Separate exact rational checks of examples supplement the complete
formal theorem; they do not substitute for its universal quantifiers.

### Transitive axioms

The literal
[transitive axiom report](https://github.com/erenup/two-vertex-sign-regularity/blob/22fedcfb6940fd943d67f1582068ed5b9b91a83e/lean/verification/2026-10-14-axioms.log)
for `IV01.twoCheckerVertices` contains only `propext`, `Classical.choice`, and
`Quot.sound`. No `sorryAx`, unproved custom axiom or additional trust in native
execution supports the target. The
[verifier](https://github.com/erenup/two-vertex-sign-regularity/blob/22fedcfb6940fd943d67f1582068ed5b9b91a83e/lean/verify.py)
checks the source, configuration and dependency pins, compiles fresh project
objects, and rejects unexpected axiom output. Its
[control record](https://github.com/erenup/two-vertex-sign-regularity/blob/22fedcfb6940fd943d67f1582068ed5b9b91a83e/lean/verification/2026-10-14-controls.json)
records the rejection tests.

The [paper-to-Lean map](https://github.com/erenup/two-vertex-sign-regularity/blob/22fedcfb6940fd943d67f1582068ed5b9b91a83e/paper-lean-mapping/README.md)
distinguishes the complete main theorem from stronger auxiliary paper
formulations and finite example checks.

## Further partial resolution — 12 September 2026

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation.

[Theorem G](../../references/holden-interval-ave-2026-09-12/manuscripts/IV-01/result.md) proves the full interval conclusion when the directed graph of nonzero fixed entries is acyclic and fixed zero entries occupy at most one checker parity. Its scaling argument uses Adm–Garloff's Theorem 3.3 with its original attribution. [Theorem V](../../references/holden-interval-ave-2026-09-12/manuscripts/IV-01/dimension_five_theorem.md) proves the full conclusion in dimension five if there are no fixed zeros and every fully fixed adjacent two-by-two block is nonsingular, allowing cyclic fixed graphs. For larger dimensions, Theorem V controls order three only.

[The order-two reduction](../../references/holden-interval-ave-2026-09-12/manuscripts/IV-01/order_two_reduction.md) and the nonsingularity/cofactor lemma control orders one, two, and the two highest orders under the original hypotheses. The unrestricted remaining middle-minor signs are not settled. Neither sufficient condition above covers every interval in the original question, which remains unchanged below.

These partial arguments passed a separate [independent Codex AI-agent review](../../references/holden-interval-ave-2026-09-12/verification/IV-01-review.md). [Submission record, verified affiliation and exact certificates](../../references/holden-interval-ave-2026-09-12/README.md). AI assistance is disclosed; finite certificates support examples rather than prove the universal theorem. No historical priority, external human peer review or formal verification is claimed. No Lean verification was performed.

## Problem statement

For $`\epsilon\in\{-1,1\}^n`$, call a real $`n\times n`$ matrix $`M`$
**nonsingular sign regular with signature** $`\epsilon`$ if $`\det M\ne0`$ and
every minor of order $`k`$ has determinant $`d`$ satisfying $`\epsilon_k d\ge0`$,
for every $`1\le k\le n`$.

Let $`n\ge5`$ and let $`L,U\in\mathbb R^{n\times n}`$ satisfy $`L\le U`$
entrywise. Define the two checkerboard vertex matrices

```math
A^-_{ij}=\begin{cases}L_{ij},&i+j\text{ even},\\U_{ij},&i+j\text{ odd},\end{cases}
\qquad
A^+_{ij}=\begin{cases}U_{ij},&i+j\text{ even},\\L_{ij},&i+j\text{ odd}.\end{cases}
```

### Question

If $`A^-`$ and $`A^+`$ are nonsingular sign regular with the same
signature $`\epsilon`$, must every real matrix $`M`$ with $`L\le M\le U`$ be
nonsingular sign regular with signature $`\epsilon`$?

The implication would certify a property of an entire interval of matrices
from only two of its vertices. Allowing zero minors is essential to the
remaining problem.

## References

Jürgen Garloff, Mohammad Adm, and Jihad Titi,
[*A Survey of Classes of Matrices Possessing the Interval Property and Related Properties*](https://www.reliable-computing.org/reliable-computing-22-pp-001-014.pdf),
Reliable Computing **22** (2016), 1–14, Conjecture 3.1, p. 7. Adm and Garloff,
[*Certification of the Sign Regularity of Matrix Intervals*](https://doi.org/10.1007/s44146-026-00223-y),
Acta Scientiarum Mathematicarum, published January 17, 2026, §3, especially
the question following Theorem 3.2 and the discussion of admissible signatures.

## Earlier status evidence — 2026-09-08

The 2026 survey explicitly retains this question. It
records positive results for strictly sign regular matrices, totally
nonnegative matrices, tridiagonal matrices, and certain signatures covering
all orders at most four. Theorem 3.3 also covers intervals whose fixed entries
$`L_{ij}=U_{ij}`$, if any, all have the same parity of $`i+j`$; fixed entries of
both parities are allowed in the general question. It also records
counterexamples when nonsingularity is omitted. Searches for sign-regular interval conjectures and subsequent
2026 results found no resolution of the displayed implication.

## Audit update — 2026-09-10

Rechecked the [2026 survey](https://link.springer.com/article/10.1007/s44146-026-00223-y), §3, Theorems 3.2–3.3 and the intervening open question. Tridiagonal and certain signature classes, as well as the specified restrictions on fixed-entry parity, prove substantive subclasses even for $`n\ge5`$. The unrestricted nonsingular case remains explicitly open there. Searches for subsequent sign-regular interval certification results found no general resolution; the status now exposes these partial results.
