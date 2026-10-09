# MD-04: exact statement specification

Author: OpenAI Codex agent `/root` (AI). Phase: preimplementation specification; no Lean target has been implemented or proved.

Canonical source: `matrix-discrepancy-and-optimization/MD-04/README.md` at `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`. SHA-256: `a8be36a5217cb0b3031c8f87cfc25e5421ca78dd8c42ecc151219fa62eb8156e`. The byte-for-byte complete original README is retained as [ORIGINAL.md](ORIGINAL.md); it includes the original question, resolution context, authors, and references. Permanent ID and canonical source are unchanged.

## Exact mathematical and numerical target

Quantifiers, in order: there exists a real C > 0 such that for all natural m,n,t with 0 < m, 0 < n, 1 <= t, and t <= m, and every real m-by-n matrix A whose entries are each 0 or 1, if each column sum is at most the real cast of t, there exists a real vector x of length n whose entries are each -1 or 1 and such that every row i satisfies |sum_j A i j * x j| <= C * sqrt((t : real)).

C precedes dimensions and sparsity. The source's integer t with 1 <= t <= m is exactly represented by such natural t. Every column receives a sign, including zero columns. No online information restriction or algorithmic requirement is present. The row-wise inequality is exactly the infinity-norm bound for positive m. Real.sqrt denotes the nonnegative real square root, and its argument is positive here. Sparsity is the ordinary sum of the 0-or-1 entries, not signed cancellation or an arbitrary norm.

Numerical data: entries {0,1}; signs {-1,1}; t >= 1 inclusive; t <= m inclusive; non-strict column and discrepancy inequalities. The stronger cited value 3*sqrt(2*pi) is not substituted for the existential C. No floating point, interval boxes, probability, or certificates are needed to state the problem.

## Planned Lean representation and review obligations

`NLA.Statements.MD04.Target : Prop` will be a definition of the full proposition, not a theorem asserting its truth. Finite dimensions use `Fin n`, finite sums use the full finite index type, and arithmetic uses Mathlib real numbers. There will be no target axiom, `sorry`, user-supplied semantics, unrestricted oracle, or unconstrained predicate standing in for the mathematics.

Review the quantifier order, every endpoint, degenerate input, real field, and correspondence of the expanded elementary formulas with the original. Two independent AI-agent specification approvals are required before Lean implementation. A later pair of Lean-boundary reviews must bind the actual definition and frozen snapshot bytes.

## Computation plan

The statement has no numerical proof obligation. Exact algebraic definitions suffice. The shared pinned LeanCert kernel-mode smoke test checks infrastructure; it is not evidence proving this target. Future numerical proof steps, if any, must select kernel trust and retain the full reviewed domain.

## Scope and attribution

This campaign adds a faithful statement only. The existing Solved status, mathematical authorship and informal-review qualifications remain those in ORIGINAL.md. No new proof, independent proof audit, human endorsement, Linux Comparator run, or status promotion is claimed.
