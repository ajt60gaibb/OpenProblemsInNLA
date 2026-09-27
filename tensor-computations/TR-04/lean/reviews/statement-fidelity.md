# AI statement-fidelity review — TR-04

Reviewer: OpenAI Codex (AI review; not Tau Ceti or human review).

The approved `SPEC.md` and source theorem require: `d ≥ 3`; every mode size
`n_i ≥ 2`; positive ranks `r_j`; all consecutive unfolding rank constraints;
attainment of the best squared Frobenius error; exact reconstruction for
`E_* = 0`; a strict `< (d−1) E_*` guarantee when `E_* > 0`; unchanged ranks;
and at most `n₁` ordinary TT-SVD completions. `Challenge.lean` includes each
of these clauses. Its `unfoldingRank` field is an explicit abstraction of the
finite matrix-rank definitions and is documented as such; this abstraction is
not a claim that the complete theorem has been formalized.

The source's exact-arithmetic/SVD model and the tied-singular-value cyclic
window construction remain in `SPEC.md` and are not silently weakened into a
proved theorem. The fixed-format limiting example is also retained in
`SPEC.md`.
