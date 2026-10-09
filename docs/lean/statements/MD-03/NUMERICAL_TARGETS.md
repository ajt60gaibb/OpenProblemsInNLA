# MD-03: exact statement specification

Author: OpenAI Codex agent `/root` (AI). Phase: preimplementation specification; no Lean target has been implemented or proved.

Canonical source: `matrix-discrepancy-and-optimization/MD-03/README.md` at `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`. SHA-256: `3486bfa69ba99b106dfb059866d0f4fa3e0b9eac99276a05f911756639bbfd1e`. The byte-for-byte complete original README is retained as [ORIGINAL.md](ORIGINAL.md); it includes the original question, resolution context, authors, and references. Permanent ID and canonical source are unchanged.

## Exact mathematical and numerical target

Quantifiers, in order: there exists a real C > 0 such that for every m,n in the natural numbers with 0 < m and 0 < n, and every real m-by-n matrix A, if for every column j the sum over i of (A i j)^2 is at most 1, there exists a real vector x of length n with every x j equal to -1 or 1 and for every row i the absolute value of the sum over j of A i j * x j is at most C.

C is chosen before all dimensions and matrices. No positivity is imposed on matrix entries. The signs are chosen after the entire A is known. There is no randomized, constructive, or runtime requirement. All rows must satisfy the bound simultaneously. Positive dimensions exclude empty maxima. The pointwise finite row bound is exactly the original infinity-norm inequality, not a Frobenius or spectral norm. Entries, sums, and C are real; C is an ordinary finite real, not an extended real.

Numerical data: the column squared-norm bound is exactly 1, the signs exactly {-1,1}, and the final bound is weak (<=). The source resolution gives a stronger strict bound with 3*sqrt(2*pi), but the target retains existential C; inserting that value would strengthen the original target. No numerical certificate is required to state the problem.

## Planned Lean representation and review obligations

`NLA.Statements.MD03.Target : Prop` will be a definition of the full proposition, not a theorem asserting its truth. Finite dimensions use `Fin n`, finite sums use the full finite index type, and arithmetic uses Mathlib real numbers. There will be no target axiom, `sorry`, user-supplied semantics, unrestricted oracle, or unconstrained predicate standing in for the mathematics.

Review the quantifier order, every endpoint, degenerate input, real field, and correspondence of the expanded elementary formulas with the original. Two independent AI-agent specification approvals are required before Lean implementation. A later pair of Lean-boundary reviews must bind the actual definition and frozen snapshot bytes.

## Computation plan

The statement has no numerical proof obligation. Exact algebraic definitions suffice. The shared pinned LeanCert kernel-mode smoke test checks infrastructure; it is not evidence proving this target. Future numerical proof steps, if any, must select kernel trust and retain the full reviewed domain.

## Scope and attribution

This campaign adds a faithful statement only. The existing Solved status, mathematical authorship and informal-review qualifications remain those in ORIGINAL.md. No new proof, independent proof audit, human endorsement, Linux Comparator run, or status promotion is claimed.
