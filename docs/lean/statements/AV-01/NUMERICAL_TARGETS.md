# AV-01 — exact mathematical and numerical specification

## Review and implementation state

This is a **preimplementation specification draft**, authored by OpenAI Codex AI agent `/root/statement_design` on
2026-09-28. Two independent statement reviews remain required. No Lean declaration
or proof is implemented by this draft. The canonical status remains **Solved**
on the previously recorded evidence; this file makes no new verification claim.

The complete canonical target copied below governs this specification. Its raw
file hash preserves the resolution and historical notes as well. Supporting
lemmas or stronger results must not replace the original target. Historical
manuscripts may quote hashes of earlier submission bodies; those are different
objects from the raw-byte source hashes recorded here.

An uninterpreted probability, norm or algorithm oracle, an assumed answer, or a
predicate defined to mean the desired conclusion is not a formalization. All
actual definitions must be independently reviewed. A statement is not a proof.

## Frozen canonical identity

- Permanent ID: `AV-01`.
- Canonical README: `intervals-and-absolute-value-equations/AV-01/README.md`.
- Frozen repository revision: `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`.
- Source status at that revision: `Solved`.
- Existing-statement check: no `.lean` files under `intervals-and-absolute-value-equations/AV-01/`.

| Source file | Raw-byte SHA-256 |
| --- | --- |
| `intervals-and-absolute-value-equations/AV-01/README.md` | `68205f4476868847a9332d5ab294d062882302f203e6903f4da3c43f61f5f091` |
| `intervals-and-absolute-value-equations/AV-01/problem.tex` | `0dab4df62838d1a578897bbc6695d6557a103f6448f78bc0347f1f4a668124a8` |
| `references/colbrook-intervals-2026-09-11/manuscripts/AV-01.tex` | `d4a45aa172ee0c0947715302eaded5efb1cb15ab528337575709d495e1c49b71` |

## Exact target and quantifier order

For every integer \(n\ge1\), rational \(A\in\mathbb Q^{n\times n}\), and rational
\(b\in\mathbb Q^n\), using exact rational embeddings, let
\[
S(A,b)=\{x\in\mathbb R^n:\ \forall i,\ \sum_j A_{ij}x_j+|x_i|=b_i\}.
\]
The decision answer is true precisely when this set has **exactly \(2^n\)
distinct points**. A faithful predicate is existence of a bijection from
`Fin (2^n)` to the solution subtype. A finite-cardinality API is acceptable
if it explicitly handles infinite sets correctly. Infinite solution sets are
negative instances; no finiteness promise is permitted.

The complete affirmative classification is existence of one finite-description
deterministic Turing machine, one natural \(C\ge1\), and one natural \(k\), all
independent of the input, such that on every valid binary encoding \(w\) of
\((n,A,b)\) it halts in at most \(C(\operatorname{length}(w)+1)^k\) steps and
returns the above Boolean. Dimension and every rational numerator/denominator
bit contribute to input length. No solution enumeration is requested.
Nonsingularity, regularity, genericity, boundedness, positive \(b\) and finite
solution count are not input assumptions.

The canonical binary rational Turing model must be represented concretely.
A signed-numerator, positive-denominator binary representation is allowed;
encoding review must justify its usual polynomial relation to the selected
shared encoding. No translator implementation is needed merely to state the
machine-existence proposition. Unit-cost rational
or real arithmetic is not equivalent here. The existential runtime constants
express ordinary polynomial bit complexity, not strong polynomiality.

## Complete source correspondence

The archived Colbrook manuscript, Theorem 1, gives the exact characterization
\[
|S(A,b)|=2^n \iff
(\forall i,\ b_i>0)\ \land\ P\text{ bounded}\ \land\
(\forall y\in P,\forall i,\ b_i-(Ay)_i>0),
\quad
P=\{y:(A+I)y\le b,\ (A-I)y\le b\}.
\]
All inequalities are coordinatewise, variables are real, strict inequalities
remain strict, and boundedness is Euclidean boundedness. The left side includes
finiteness. Section 4 first rejects any \(b_i\le0\), then uses at most \(n+1\)
exact rational LP feasibility tests, each with \(n\) free variables, \(2n\)
inequalities and one equality:

1. Reject if \((A+I)r\le0,\ (A-I)r\le0,\ -\sum_i(Ar)_i=1\) is feasible.
2. For each \(i\), reject if \((A+I)y\le b,\ (A-I)y\le b,\ (Ay)_i=b_i\) is feasible.
3. Otherwise accept.

The recession normalization \(1\) excludes the zero direction. The face checks
use exact zero, not tolerances. Section 4 and polynomial-time rational LP supply
the complexity conclusion. The characterization alone, or correctness relative
to a free LP oracle, is only an intermediate result. The manuscript's four-point
example and spectral radius \(6/5\) are diagnostics, not target restrictions.

Original source: Milan Hladík, *Absolute value equations with 2^n solutions*,
§2.3 and §7. Resolution source: Matthew J. Colbrook, archived manuscript,
Theorem 1 and Section 4. Authorship and informal-review scope are preserved by
the canonical README.

## Definitions needed for the Lean statement

**Concrete binary encodings, finite deterministic Turing-machine semantics,
bounded-step execution and Boolean output decoding are required.** With these
definitions, the complete statement is simply a closed proposition asserting
existence of a machine and polynomial bound with the specified behavior on
every valid input. The author need not implement such a machine to define
that proposition.

Review the actual input-length function and machine steps so that ordinary
binary bit complexity is expressed, not unit-cost rational arithmetic.
Malformed inputs may be rejected; every well-formed input is covered.
An uninterpreted complexity predicate or the LP characterization alone would
omit the target. A concrete definition of polynomial-time decision, however,
is sufficient to state it without proving that this language belongs to P.

Polynomial-time rational LP, correctness of the displayed algorithm, and
closure/cost bounds for composing its calls are obligations for a later proof
of the affirmative resolution. They are **not prerequisites for the
statement-only definition**, and no LP solver API is required merely to
state the machine-existence proposition.

## Numerical work and verification boundary

No interval computation is required to state the problem. Retain exact constants,
all quantified inputs and every endpoint. A later certificate must use the shared
pinned LeanCert dependency, `set_option leancert.trust "kernel"`, explicit
`leancert (trust := kernel)` and `#assert_trust kernel` for exported results.
Symbolic statements need no artificial numerical calculation. Finite sample checks
or floating-point experiments cannot replace universal claims.

The eventual Lean boundary needs a type check and fresh review of all definitions.
Comparator statement identity is a separate mechanical gate; it cannot establish
fidelity to this prose. Challenge placeholders must never enter a purported proved
Solution. No build or placeholder identity comparison promotes the canonical status.

## Verbatim canonical target

The following target portion is copied exactly from the canonical README. The
full source hash above also preserves its resolutions and historical context.

<!-- canonical-target-start -->
## Context and notation

Absolute values and vector inequalities are componentwise. All algorithmic questions use rational input in binary and the deterministic Turing model. Input length includes the matrix dimensions and the bit lengths of all rational coefficients.

## Problem statement

For input $`A\in\mathbb Q^{n\times n}`$ and $`b\in\mathbb Q^n`$, $`n\ge1`$, set

```math
\Sigma_+(A,b)=\{x\in\mathbb R^n:Ax+|x|=b\}.
```

### Question

Classify the computational complexity of deciding whether

```math
|\Sigma_+(A,b)|=2^n.
```

In particular, is this decision problem in $`\mathsf P`$, or can an $`\mathsf{NP}`$-hardness or $`\mathsf{coNP}`$-hardness classification be established by polynomial-time many-one reductions? The task returns one Boolean answer. Infinite solution sets are negative instances. There is no promise that the solution set is finite.

<!-- canonical-target-end -->
