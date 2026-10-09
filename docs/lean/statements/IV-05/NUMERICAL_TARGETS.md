# IV-05 — exact mathematical and numerical specification

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

- Permanent ID: `IV-05`.
- Canonical README: `intervals-and-absolute-value-equations/IV-05/README.md`.
- Frozen repository revision: `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`.
- Source status at that revision: `Solved`.
- Existing-statement check: no `.lean` files under `intervals-and-absolute-value-equations/IV-05/`.

| Source file | Raw-byte SHA-256 |
| --- | --- |
| `intervals-and-absolute-value-equations/IV-05/README.md` | `09f68840d5c42b3b101532620a8900a7253f6f881bfa59ad99e80ff21c16a87c` |
| `intervals-and-absolute-value-equations/IV-05/problem.tex` | `001b734a85c728ecd14746f6c6214a87ee47d1d28d6657c2ba8901c44a2e4009` |
| `references/colbrook-intervals-2026-09-11/manuscripts/IV-05.tex` | `f216995a9834671695809c9b2290503da9ff289bb37a26e61247eb33be4b65cc` |

## Exact target and quantifier order

For every \(n\ge1\), input rational matrices \(L\le U\) and vectors \(l\le u\),
all inequalities entrywise. Every bit of the dimensions and coefficients
counts in the binary input length. Define independent-entry real intervals
\[
\mathcal A=\{A:L\le A\le U\},\qquad \mathcal b=\{b:l\le b\le u\}.
\]
The promise quantifies over every real \(A\in\mathcal A\): it is invertible
and \(A^{-1}\) is a nonsingular M-matrix. Concretely, \(A^{-1}\) is invertible,
its off-diagonal entries are nonpositive, and \((A^{-1})^{-1}\) is entrywise
nonnegative. Equivalently under invertibility, \(A\ge0\) entrywise and
\((A^{-1})_{ij}\le0\) for \(i\ne j\). If this equivalent definition is used,
its equivalence must be checked; positivity of inverse diagonal entries is
derived, not added as an input restriction.

Let
\[
\Sigma=\{x\in\mathbb R^n:\exists A\in\mathcal A,\exists b\in\mathcal b,\ Ax=b\}.
\]
The complete conclusion is existence of a uniform finite-description
deterministic Turing transducer and polynomial binary-time bound which, on
every valid promised encoding, returns **exact rational** vectors \(a,z\)
such that for every coordinate \(i\),
\[
\forall x\in\Sigma,\ a_i\le x_i\le z_i,\qquad
\exists x^-\in\Sigma,\ x^-_i=a_i,\qquad
\exists x^+\in\Sigma,\ x^+_i=z_i.
\]
Witnesses may vary across coordinates and endpoints. This is the smallest
coordinate box, with attained minima/maxima, not an arbitrary enclosure.
There is no claim one matrix or vector attains all endpoints simultaneously.
Both rational output and polynomial bit complexity are mandatory.
Off-promise behavior is unrestricted, and promise recognition is not required.
A bound \(C_0(\operatorname{length}(w)+1)^k\), with uniform natural
\(C_0\ge1,k\), gives the intended complexity meaning.

Include \(n=1\), zero widths, zero/mixed-sign right-hand sides, zero solution
coordinates, reducible inverse-M matrices and zero off-diagonal inverse
entries. Do not impose irreducibility, positive widths, nonnegative \(b\),
or strict off-diagonal signs. Compactness/nonemptiness follow under the
promise; they do not replace the algorithmic conclusion.

## Complete source correspondence and exact LP boundary

The archived Colbrook manuscript sets
\[
C=(L+U)/2,\ R=(U-L)/2,\ b_c=(l+u)/2,\ b_r=(u-l)/2,
\quad H_\sigma(x)=Cx-D_\sigma R|x|.
\]
For coordinate \(i\), choose \(\sigma_i^+=1\) and
\(\sigma_j^+=-1\) for \(j\ne i\), with \(\sigma^-=-\sigma^+\).
Theorem 3 says the unique solution of
\[
H_{\sigma^\pm}(x)=b_c+D_{\sigma^\pm}b_r
\]
has \(i\)th coordinate the upper endpoint for \(\sigma^+\) and lower endpoint
for \(\sigma^-\). Signs at zero coordinates may be either choice.
For each of these \(2n\) problems put
\[
P=C-D_\sigma R,\quad Q=C+D_\sigma R,\quad X=Q^{-1},\quad Y=P^{-1},
\quad b=b_c+D_\sigma b_r.
\]
The LP has \(n\) free variables and \(2n\) inequalities:
\[
\min_y\mathbf1^Ty\quad\text{subject to}\quad Xy\ge0,\quad Y(y+b)\ge0.
\]
Every optimum yields \(v=Xy,\ u'=Y(y+b),\ x=u'-v\), with exact
\(u'_jv_j=0\). This \(u'\) is distinct from the input upper RHS endpoint \(u\).
Lemma 2 gives the LP correspondence, Lemma 1 the unique piecewise linear root.
Exact rational inversion, a polynomial-time rational LP algorithm and exact
postprocessing give ordinary polynomial bit complexity. Float LP tests or
exponential sign enumeration are diagnostics, not the asserted algorithm.

The inverse-M inverse signs are essential to this reduction; bijectivity under
general regularity alone does not settle AV-03. Separately enclosing \(A^{-1}\)
and multiplying by \(\mathcal b\) may lose dependence and is not this target.

Original source: Milan Hladík, *An overview of polynomially computable
characteristics of special interval matrices*, §9, question before Theorem 25.
Resolution: Matthew J. Colbrook, archived manuscript, Lemmas 1–2, Theorem 3
and Section 5.

## Definitions needed for the Lean statement

**Concrete finite deterministic Turing-transducer semantics, binary rational
input/output encodings and bounded-step execution are required.** They allow
the complete target to be defined as existence of a transducer and polynomial
bound giving the exact rational endpoint specification on every promised
input. The transducer need not be constructed to state this closed proposition.

Review that the runtime counts binary machine steps and the output decoding
is exact. The statement must retain the existence of a polynomial-time
machine; asserting only rational endpoints or the LP correspondence drops that
requirement. An assumed exact LP oracle or a unit-cost real model is not a
substitute for the concrete deterministic Turing model.

An implemented polynomial-time rational LP solver, exact inversion routines,
proofs of their complexity and the correctness of the 2n-LP algorithm are
obligations for a later proof of the affirmative resolution. They are **not
prerequisites for this statement-only definition**; a rational LP API is not
needed merely to state the transducer-existence target.

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
## Problem statement

For arbitrary $`n\ge1`$, the input consists of rational matrices $`L\le U`$ and rational vectors $`l\le u`$, with entrywise inequalities. Let

```math
\mathcal A=\{A\in\mathbb R^{n\times n}:L\le A\le U\},\qquad
\mathcal b=\{b\in\mathbb R^n:l\le b\le u\}.
```

Assume as a promise that every $`A\in\mathcal A`$ is an inverse M-matrix: $`A^{-1}`$ has nonpositive off-diagonal entries and is a nonsingular M-matrix. Here a nonsingular M-matrix means an invertible real matrix with nonpositive off-diagonal entries and entrywise nonnegative inverse. The entries of $`A`$ and $`b`$ vary independently.

Is there a deterministic algorithm that returns the exact rational endpoints of

```math
\prod_{i=1}^n
\left[\min_{A\in\mathcal A,\ b\in\mathcal b}(A^{-1}b)_i,
      \max_{A\in\mathcal A,\ b\in\mathcal b}(A^{-1}b)_i\right]
```

in time polynomial in the binary input length? Behavior outside the promise is unrestricted, and checking the promise is not part of the requested algorithm. This is the precise bit-complexity formulation of the source's efficient interval-system solution-hull question.

The promise makes the solution set nonempty and compact. The aim is its smallest coordinatewise enclosure. Computing the interval hull of $`A^{-1}`$ separately is already easier in this matrix class; multiplying that enclosure by $`\mathcal b`$ need not capture the dependence among entries of the inverse.

<!-- canonical-target-end -->
