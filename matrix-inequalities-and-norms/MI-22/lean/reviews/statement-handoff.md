# MI-22 statement-gate handoff

**Ready for two independent statement reviews. No proof has been implemented.**
The isolated branch is `codex/lean-mi22-singular-value-log-majorization` at base
`8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`. No canonical file, status, commit,
push, or PR was changed.

The freeze is `reviews/statement-freeze.json`, SHA256
`d83d2a2baa1788f6e5ec284c70bb12d7618f4963a9426777a37b2af4135ed756`.
It binds 27 candidate project files and eight original canonical/manuscript
files. This handoff report is separate from the freeze to avoid a circular hash.

| Mathematical boundary | SHA256 |
| --- | --- |
| `NLA/MI22/Definitions.lean` | `3a9398c2da3be1c71fd59de483042153cae1af55226f4b61ca9d7bd977ffd8f8` |
| `Challenge.lean` | `503cc7280458d3a1dcc4c3a03b91bcb3ae7e7940961dcd12d86736a133923179` |
| `NUMERICAL_TARGETS.md` | `3798f0d25414815e683cabfc77ab776a2a22e4929c1fab0ea4f49fbde8187c66` |
| `SOURCE_CORRESPONDENCE.md` | `e501e9b1476986cf0764067bd5672b0dbdb4261a9daf99ddcb5c7f13b548c95b` |

The complete canonical statement and complete Colbrook source proof were read;
the original primary-paper definitions and Conjecture 1.1 were separately
checked. The full target is retained: all positive dimensions, all complex
positive definite A and B, every real t in [0,1], all proper nonempty products
of the actual sorted singular values, and equality of the full products.
Actual CFC powers, Euclidean norms, multiplicity-preserving singular values,
and every required bridge are explicit in the frozen statements.

The witness is a disclosed rational adaptation, approved in principle by root.
A is unchanged. T is the source's exact rational R rounded to dyadic denominator
8192, and **B is redefined as D T⁸ D**. This is not the source's printed integer
B. George Stepaniants is credited for the formalization/adaptation with the
approved Caltech department affiliation and AI assistance; Colbrook retains
credit for the original counterexample and method. No new personal email or
historical-priority claim is added.

The exact Fraction reconstruction verifies the source-rounding provenance, LDL
identity and positive pivots, all eighth-power and product data, Euclidean unit
vector, strict trace bound, tested coordinate greater than 44000, and squared
Frobenius bound below 10500². It does not import the source verifier or use
floating-point spectral results. Reconstruction SHA256:
`3a3aa263d3c1abd59477695e76d0c1906e75c6918fe2f0699716460956b27431`.

The actual-root identities, trace-to-root norm bound, and relation `L Y=N` are
theorem conclusions, never premises. They give `‖AB‖₂<10500<11000<‖L‖₂` using
one exact unit vector. This removes approximate-root error analysis without
weakening the full original conjecture. The only planned LeanCert point check
is `10500<11000` in explicit kernel mode, consumed by the actual final strict
singular-value contradiction.

Statement build `lake build NLA.MI22.Definitions Challenge` passed, reporting
2723 jobs and only eight intentional Challenge holes. A separate fresh-prefix
run compiled Definitions, Challenge, and the actual declaration inspector,
excluding the old project artifact path. All three commands passed. All 23
definition kernel audits have exactly the standard three axioms. All ten
dependency Git trees are clean at the pinned revisions. Fresh command record
SHA256: `ba3e6dcedf3ec63a05bf19f27abc52d3778327876670581ef15c706105b86cde`.
These are macOS statement checks with pinned dependency artifacts reused, not
proof completion or Linux Comparator verification.

No statement ambiguity or failed exact certificate remains known. The important
review points are the altered witness attribution, complete original
log-majorization quantifiers/equality, actual singular-value multiplicities,
actual noncommuting CFC factor order, and the genuine trace/action/norm bridges.
After both approvals, all eight exports still require complete Lean proofs,
two independent final reviews, and the real Linux kernel/Comparator workflow.
