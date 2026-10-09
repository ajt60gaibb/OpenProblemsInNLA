# AV-02 — exact mathematical and numerical specification

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

- Permanent ID: `AV-02`.
- Canonical README: `intervals-and-absolute-value-equations/AV-02/README.md`.
- Frozen repository revision: `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`.
- Source status at that revision: `Solved`.
- Existing-statement check: no `.lean` files under `intervals-and-absolute-value-equations/AV-02/`.

| Source file | Raw-byte SHA-256 |
| --- | --- |
| `intervals-and-absolute-value-equations/AV-02/README.md` | `c3e81826d271c719b61c0b2ba102206e24d2452a4684511d87cbacb1e7224828` |
| `intervals-and-absolute-value-equations/AV-02/problem.tex` | `230b884d949a00c887830b324b9d81b0a7876d7e958020cedd5691dd6764c928` |
| `references/colbrook-intervals-2026-09-11/manuscripts/AV-02.tex` | `3538343d5fa5bff04d110bb437df8defbbf46b9fb1af46cafc4bc0bb7f32faed` |

## Exact target and quantifier order

Input consists of \(n\ge1\), \(A\in\mathbb Q^{n\times n}\), and rational \(t>0\).
For real \(d\in[-1,1]^n\), set \(M(A,d)=A-\operatorname{diag}(d)\).
The promise is
\[
\operatorname{Regular}(A)\iff
\forall d\in[-1,1]^n,\ \det M(A,d)\ne0.
\]
Only diagonal entries vary. The norm is the operator norm induced by the
Euclidean vector norm. Under the promise,
\[
c_2(A)=\max_{d\in[-1,1]^n}\|M(A,d)^{-1}\|_2.
\]
The answer is yes exactly when \(c_2(A)\ge t\); equality belongs to yes.
An equivalent witness predicate is
\(\exists d\in[-1,1]^n,\ t\le\|M(A,d)^{-1}\|_2\).
If used, its equivalence must follow from compactness, regularity and continuity,
not be assumed. There is no obligation to recognize the regularity promise.

The requested affirmative classification is **NP-hardness under polynomial-time
promise-preserving Turing reductions** in the rational binary Turing model:
for every binary language in NP, a deterministic polynomial-time oracle
reduction decides that language for every oracle agreeing with this threshold
predicate on promised inputs, and every query in every such run is a regular
matrix paired with a positive rational threshold. Off-promise oracle behavior
must be irrelevant. Dimensions and all coefficient/threshold bits count toward
input size. This asserts neither \(P\ne NP\) nor efficient recognition of the
general regularity promise.

## Complete source correspondence and exact arithmetic

The archived Colbrook manuscript proves a stronger many-one reduction from
unweighted MAX-CUT. Use a finite simple graph with \(v\) vertices, \(m\ge1\)
edges, \(1\le k\le m\), maximum cut cardinality \(C_G\), and oriented incidence
matrix \(B\in\{-1,0,1\}^{v\times m}\). Each edge column has one \(+1\) and one
\(-1\). Define
\[
N=1+v+m,\quad K=12N^2,\quad
A_G=\begin{pmatrix}2&K\mathbf1^T&0\\0&2I_v&KB\\0&0&2I_m\end{pmatrix},
\]
\[
q=\lfloor\sqrt{144N^2k}\rfloor,\qquad t_G=8N^3q.
\]
The integer square root is exact. Every perturbed diagonal lies in the closed
interval \([1,3]\), so upper triangularity proves the promise. Correctness is
\[
C_G\ge k\iff c_2(A_G)\ge t_G.
\]
The manuscript establishes
\[
96N^4\sqrt{C_G}\le c_2(A_G)\le96N^4\sqrt{C_G}+36N^3.
\]
The no branch has \(t_G-96N^4\sqrt{k-1}>40N^3>36N^3\);
the yes branch is non-strict. This includes \(k=1\), isolated vertices and
disconnected graphs. Trivial MAX-CUT inputs outside the restriction must map
to fixed legal yes/no instances, rather than be deleted from the source language.

The source also proves NP-completeness on rational upper-triangular diagonal-2
matrices. A sign-vector certificate uses failure of positive definiteness of
\(t^2(A-\operatorname{diag}s)^T(A-\operatorname{diag}s)-I\);
zero eigenvalues are accepted. This restricted NP-membership assertion does
not classify recognition of the general regularity promise. The original
target needs hardness only. A later proof via this route must connect the
MAX-CUT correctness equivalence to NP-hardness and polynomial construction
cost; these proofs are not required to define the original proposition.

Original source: Moslem Zamani and Milan Hladík, *Error bounds and a condition
number for the absolute value equations*, §2 and §2.1. Resolution: Matthew J.
Colbrook, archived manuscript, Theorem 2 and Sections 2–3. Journal and arXiv
vertex-lemma numbering differ; the explicit mathematical boundary above controls.

## Definitions needed for the Lean statement

**Concrete finite-machine, binary-encoding, NP-language, oracle-execution and
polynomial-time definitions are required.** Define the exact regular-input
promise and threshold language mathematically, then quantify over all NP
languages and finite oracle Turing reductions, bounding their steps and
requiring valid promised queries on every run with a correct promised oracle.
This is a complete closed target proposition without implementing any reduction.

An oracle is intrinsic to the specified Turing-reduction model, but its input,
answer and unit-query-step semantics must be concrete and its permitted
answers must agree with the displayed threshold predicate on the promise.
It is not an unconstrained oracle for the entire conclusion. Likewise, a
custom hardness predicate defined only as the MAX-CUT numerical equivalence
would omit the original universal complexity statement.

MAX-CUT NP-hardness, an explicit graph-to-matrix reduction, polynomial-time
integer square root, polynomial construction costs, and correctness of the
spectral gap are obligations of a later resolution proof. They are **not
prerequisites for defining the original NP-hardness proposition**. Exact
rational/polynomial separation can reduce the work of that later proof;
finite graph experiments cannot prove NP-hardness.

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

For a real square matrix $`A`$, define the diagonal perturbation family

```math
\mathcal D(A)=\{A-\mathop{\mathrm{diag}}\nolimits(d):d\in[-1,1]^n\}.
```

Call this family **regular** when every member is nonsingular. Only diagonal entries vary. This is precisely the entrywise interval matrix $`[A-I_n,A+I_n]`$.

## Problem statement

Let $`n\ge1`$ and let $`A\in\mathbb Q^{n\times n}`$ be promised to have regular $`\mathcal D(A)`$. Define

```math
c_2(A)=\max_{d\in[-1,1]^n}
\left\|(A-\mathop{\mathrm{diag}}\nolimits(d))^{-1}\right\|_2
=\left(\min_{d\in[-1,1]^n}
\sigma_{\min}(A-\mathop{\mathrm{diag}}\nolimits(d))\right)^{-1}.
```

### Question

Is deciding $`c_2(A)\ge t`$, given such an $`A`$ and a positive rational threshold $`t`$, $`\mathsf{NP}`$-hard under polynomial-time Turing reductions that query only inputs satisfying the regularity promise?

This is a decision formulation of the published hardness conjecture. Equality belongs to the yes case. Checking the promise is outside the task. The spectral norm is the operator norm induced by the Euclidean vector norm.

<!-- canonical-target-end -->
