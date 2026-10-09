# RA-10 — exact mathematical and numerical specification

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

- Permanent ID: `RA-10`.
- Canonical README: `randomized-and-low-rank-approximation/RA-10/README.md`.
- Frozen repository revision: `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`.
- Source status at that revision: `Solved`.
- Existing-statement check: no `.lean` files under `randomized-and-low-rank-approximation/RA-10/`.

| Source file | Raw-byte SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/problem.tex` | `64242adb46d4683e3841c7a3a3d0013112f408ac905b86ee938c9abf40182bb0` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `randomized-and-low-rank-approximation/RA-10/solution.tex` | `ec2ae9f759e2df80b022ed5f523d0fecc813e6faa62cbae00271af6c82ccd48f` |

## Exact target and quantifier order

The original proposition is existence of a real \(C\ge1\) such that for every
\(n\ge2\), \(1\le k<n\), real symmetric PSD \(A,\widehat A\), real
\(\varepsilon\ge0\), continuous nonnegative operator-monotone \(f\) on
\([0,\infty)\), and every allowed ordered orthonormal eigendecomposition,
\[
\|A-\widehat A_k\|_*\le(1+\varepsilon)\|A-A_k\|_*
\ \Longrightarrow\
\|f(A)-f(\widehat A)_k\|_*\le(1+C\varepsilon)\|f(A)-f(A)_k\|_*.
\]
The existential \(C\) precedes all input quantifiers and is independent of
\(f\) too. The archived solution gives the concrete stronger witness \(C=11\).
If both original and stronger statements are exported, name them separately
and explicitly connect them. Neither optimality of 11 nor another norm is
claimed.

## Concrete definitions

PSD means real symmetry and \(v^TXv\ge0\) for every real vector \(v\).
\(H\succeq G\) means \(H-G\) is PSD. Operator monotonicity means **for every
matrix size** and every real symmetric \(H\succeq G\succeq0\),
\(f(H)\succeq f(G)\). Scalar monotonicity or scalar concavity is insufficient.

One faithful Lean function model is \(f:\mathbb R\to\mathbb R\), continuous
on the closed nonnegative half-line and nonnegative there, with negative
arguments unused. A function on the nonnegative subtype is equivalent with
the topology explicit. Unexplained continuity on all reals would strengthen
the original hypothesis.

For PSD \(X\), an allowed decomposition consists of a real orthogonal matrix
with columns \(q_i\), eigenvalues \(\lambda_1\ge\cdots\ge\lambda_n\ge0\), and
\(X=\sum_i\lambda_iq_iq_i^T\). Define
\[
f(X)=\sum_{i=1}^n f(\lambda_i)q_iq_i^T,\quad
X_k=\sum_{i=1}^k\lambda_iq_iq_i^T,\quad
f(X)_k=\sum_{i=1}^k f(\lambda_i)q_iq_i^T.
\]
Full functional calculus is decomposition-independent; truncated calculus
retains the selected basis. Quantify over decompositions of both matrices,
with independent choices for \(A\) and \(\widehat A\), but use the **same**
selected decomposition in both truncations of each matrix. No fixed
tie-breaking rule may silently replace this universal statement.

The nuclear norm is the sum of singular values, the nonnegative square roots
of the eigenvalues of \(M^TM\). For symmetric differences, the sum of absolute
eigenvalues is equivalent, with the correspondence checked. Entrywise sum,
Frobenius or operator norms, or trace of an indefinite matrix, are not substitutes.

## Endpoints and complete source correspondence

Include \(\varepsilon=0\), zero matrices, rank below \(k\), zero selected
eigenvalues, all ties including at \(k\), \(f(0)>0\), constant functions and
zero optimal tails. There is no ordering, commutation, invertibility or
spectral-gap hypothesis. In particular \(f(\widehat A)_k\) need not equal
\(f(\widehat A_k)\) when \(f(0)>0\).

The archived Stepaniants Theorem 1 provides 11 on precisely this full domain.
Its Sections 2–4 use all ridge atoms \(x/(s+x)\), \(s>0\), an exact compression
factor 2, an intermediate factor 5, then 11. Section 5 adds the constant and
linear terms and positive integral representation, and handles zero input
tail without division by it. These are proof data; they do not justify
restricting \(f\), parameters, eigenspaces, or matrices.

A later proof must retain the selected rank-\(k\) projection \(P\) when
the truncated matrix has smaller rank. The source's \(f(B)_P\) applies
functional calculus on range \(P\) and zero on its complement, preserving
selected zero eigenvectors. Arbitrarily shrinking support loses target cases.

Original source: Persson, Meyer and Musco, *Algorithm-agnostic low-rank
approximation of operator monotone matrix functions*, §1.2 and closing §5;
[pinned v2](https://arxiv.org/html/2311.14023v2) inspected 2026-09-28.
Resolution: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology. The earlier commuting result
and lower bound \(C\ge2\) remain separately credited on the canonical page.

## Preimplementation review obligations

Inspect the all-size operator-monotonicity definition, each quantified basis,
actual nuclear norm and quantifier order. The mathematical target is fully
specified. Existing spectral calculus may be reused only after checking its
conventions; no decimal approximation belongs in the assumptions.

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
Does a universal constant $`C\ge1`$ exist with the following property? For every $`n\ge2`$, $`1\le k< n`$, real symmetric positive semidefinite matrices $`A,\widehat A\in\mathbb R^{n\times n}`$, $`\varepsilon\ge0`$, and continuous operator-monotone function $`f:[0,\infty)\to[0,\infty)`$,

```math
\|A-\widehat A_k\|_*\le(1+\varepsilon)\|A-A_k\|_*
```

implies

```math
\|f(A)-f(\widehat A)_k\|_*\le(1+C\varepsilon)\|f(A)-f(A)_k\|_*?
```

Here $`\|M\|_*=\sum_i\sigma_i(M)`$ is the nuclear norm. Operator monotonicity means $`f(H)\succeq f(G)`$ for every size and every real symmetric $`H\succeq G\succeq0`$; functions of matrices are defined spectrally. No ordering between $`A`$ and $`\widehat A`$ is assumed.

For an ordered orthonormal eigendecomposition $`X=\sum_{i=1}^n\lambda_iq_iq_i^T`$ of a PSD matrix, set

```math
X_k=\sum_{i=1}^k\lambda_iq_iq_i^T,
\qquad f(X)_k=\sum_{i=1}^kf(\lambda_i)q_iq_i^T.
```

The assertion must hold for every choice of ordered eigenvectors, using the same choice in both truncations. $`C`$ must be independent of all inputs, including $`f`$.

This is the nuclear-norm instance of the authors' explicit question about a fixed loss in approximation accuracy. It asks whether the ordering condition in existing transfer results can be removed at a controlled price.

<!-- canonical-target-end -->
