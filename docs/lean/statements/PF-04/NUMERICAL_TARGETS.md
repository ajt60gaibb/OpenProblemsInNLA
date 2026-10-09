# PF-04: exact statement specification

Author: OpenAI Codex agent `/root` (AI). Phase: preimplementation specification; no Lean target has been implemented or proved.

Canonical source: `nonnegative-and-positive-factorizations/PF-04/README.md` at `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`. SHA-256: `acbf30a432e4ee1898661c05a9efc2f24f9ec32183da33836315b58e6c46e08a`. The byte-for-byte complete original README is retained as [ORIGINAL.md](ORIGINAL.md); it includes the original question, resolution context, authors, and references. Permanent ID and canonical source are unchanged.

## Exact mathematical and numerical target

A factor predicate Factor(A,r) means there is a real 6-by-r matrix B whose every entry is nonnegative and such that for all row indices i,j, A i j = sum over k in Fin r of B i k * B j k. The empty sum at r=0 is zero. CompletePositivity(A) means there exists some natural r with Factor(A,r). This is the actual Gram-factor definition, not merely positive semidefinite plus entrywise nonnegative. It implies symmetry without restricting away any completely positive input.

The complete equality formulation is the conjunction of: (1) for every real 6-by-6 matrix A, CompletePositivity(A) implies Factor(A,9); and (2) there exists a real 6-by-6 matrix A such that CompletePositivity(A) and for every natural r < 9, not Factor(A,r).

The universal nine-column assertion is the question's explicit equivalent formulation; the second conjunct retains the established sharpness in its displayed maximum-equals-nine formulation. Together they express exactly maximum cp-rank nine, without a totalized minimum that could assign misleading values to non-CP matrices. Zero columns pad any factor of width <=9 to width 9. The lower-bound witness need not be positive definite, because the original target does not impose that strengthening. It is not restricted to a graph support, positive entries, nonsingular matrices, the boundary, or an exceptional copositive face. Zero A is included and admits width zero; the lower-bound witness is automatically nonzero.

Numerical data: order exactly 6, upper factor width exactly 9, strict r < 9 for every smaller width, real entries with non-strict nonnegativity, exact factor equality. No approximate factorization, runtime, interval arithmetic or tolerance is part of the original target. The known lower bound is retained as part of the full proposition, not assumed as an axiom.

## Planned Lean representation and review obligations

`NLA.Statements.PF04.Target : Prop` will be a definition of the full proposition, not a theorem asserting its truth. Finite dimensions use `Fin n`, finite sums use the full finite index type, and arithmetic uses Mathlib real numbers. There will be no target axiom, `sorry`, user-supplied semantics, unrestricted oracle, or unconstrained predicate standing in for the mathematics.

Review the quantifier order, every endpoint, degenerate input, real field, and correspondence of the expanded elementary formulas with the original. Two independent AI-agent specification approvals are required before Lean implementation. A later pair of Lean-boundary reviews must bind the actual definition and frozen snapshot bytes.

## Computation plan

The statement has no numerical proof obligation. Exact algebraic definitions suffice. The shared pinned LeanCert kernel-mode smoke test checks infrastructure; it is not evidence proving this target. Future numerical proof steps, if any, must select kernel trust and retain the full reviewed domain.

## Scope and attribution

This campaign adds a faithful statement only. The existing Solved status, mathematical authorship and informal-review qualifications remain those in ORIGINAL.md. No new proof, independent proof audit, human endorsement, Linux Comparator run, or status promotion is claimed.
