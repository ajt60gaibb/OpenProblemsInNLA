# IS-03 statement-only handoff

**FROZEN; ready for two independent statement reviews. No proof is implemented.**

Project: `eigenvalues-and-inverse-problems/IS-03/lean`, isolated worktree
`/tmp/nla-lean-is03-worktree`, branch `codex/lean-is03-derivative-realizability`.
Base: `f41f1f9ffa2171550d4bb795862c6170c4f26070`. Canonical status remains **Solved**.
Statement authors are `/root` and `/root/solved_statement_inventory`; neither
counts as an independent statement referee for this package. Assigned
independent reviewers are `/root/leancert_examples` and
`/root/formal_review_standards`. No approval is asserted here.

## Exact boundary and source identity

The freeze binds **34 project files and 10 original source Git blobs**.
Its own digest and this handoff's digest are sent separately to the reviewers.

| File | SHA-256 |
| --- | --- |
| `reviews/statement-freeze.json` | `588196a54decb127a814dc4860621505d6874a077295f3e30a782d7f28b8ac6c` |
| `NLA/IS03/Definitions.lean` | `8b4b581e9831b0438d0635b013a60df0cf0139fa9087850b842d8e58975ea1a9` |
| `Challenge.lean` | `4a8817f7c983819fac0a9206092831e72709fcfdb73b0687350914162ef23440` |
| `NUMERICAL_TARGETS.md` | `b1fe777e2d4853b4d60d75e4d0628939f19434434ca82ac4ffe2a3e5bdbf1787` |
| `comparator.json` | `f1e84761b1175d1d638b6cc26c2c2797c7da64ca7dd73919594437388484bf0a` |
| `source-inputs.json` | `dec263f906d2dbbaa2351e3efa20a60398b8bf1ae8a40cbf446d348a80530e40` |
| `reviews/statement-evidence/input-audit.json` | `2de9e2f64f34c4631e3fa724ef0d02c7641faff408e5fc8806db9eb157d9e2da` |

The complete original manuscript remains
`548553e2f177da2a2c5135030c6a34fff761d2b9c800b246b7f9a6797e02d45c` (5,068 bytes).
The authored source, original target, original review and submission history
remain byte-identical to their bound Git blobs. All canonical files, shared
infrastructure and the user's checkout were left unchanged. No commit, push,
index regeneration or status change was made.

## Actual checks

Three fresh direct Lean source commands passed on macOS: Definitions,
Challenge and actual semantic/API inspection. Only the seven deliberate
Challenge `sorry` warnings occurred. The inspection confirms genuine
`Matrix.semiring` powers, `Matrix.trace`, determinant-based `Matrix.charpoly`,
real polynomial derivative/scalar action and the all-order quantifiers. Three
definition-only LeanCert kernel/standard-three dependency checks passed;
these certify no Challenge theorem and execute no numerical certificate.

The run used a new empty project prefix and ten clean dependency repositories
at the manifest pins, with MI-22 dependency objects reused read-only. No old
IS-03 object or prior project prefix was in `LEAN_PATH`. No dependency was
copied or rebuilt. This is not a local Lake build or a Linux Comparator run.

- Fresh run record: `2e8e3dc28f8d5f4a82c9df96f2c15a313f406a22a8d706442a9b758bdb652909`.
- Raw semantic inspection: `1f53722d104076bb3583b88581ea95fe4454bc5cd71cc2cfcb646971c1bb8dba`.
- Exact diagnostic: `95a88f07c3c97262f2fad447227257741afe65bc483304412876e8881371c370`.
- Input/coverage/pin/source audit: `2de9e2f64f34c4631e3fa724ef0d02c7641faff408e5fc8806db9eb157d9e2da`.

The independent rational diagnostic parses the actual Lean literals. Sparse
characteristic determinants use four supported witness permutations and six
companion permutations. Formal differentiation yields the stated monic
sextic; Newton recurrence and independent companion powers agree on all
seven moments, ending at `-8593/823543`. The companion check is explicitly
one finite diagnostic and cannot prove the universal trace-moment contract.
Permanent-ID validation against `origin/main` and all **17** ID tests passed.
The tracked worktree diff is empty; only this new project is untracked.

## Review focus and later obligations

The seven exports retain the complete original normalized-derivative
realizability conjecture and its negation. Every real potential realizing
matrix has only the actual characteristic-polynomial equality as a premise
in the trace-moment contract. There is no diagonalizability, simple-spectrum,
zero-trace, symmetry or irreducibility restriction. The unchanged admissible
source witness has order seven and trace one half. The final order-six
nonrealizability negates the entire all-`n≥5` assertion.

The actual arbitrary-matrix trace-power bridge remains substantial unproved
work. Pinned Mathlib has `MvPolynomial.psum_eq_mul_esymm_sub_sum`, elementary
symmetric evaluation, genuine block/trace characteristic-polynomial lemmas
and Cayley–Hamilton, but an implementation must still connect these to the
actual matrix powers. The inspected APIs and their limitations are in
`reviews/statement-evidence/API_NOTES.md`. No bridge may become an axiom,
added premise or companion-only surrogate.

After two independent statement approvals, the planned material kernel
LeanCert scalar target is `(-8593/823543 : ℝ) < 0`. All polynomial, matrix,
trace and logical steps require exact proofs. There is currently no
`Proof.lean` or `Solution.lean`. `Solution` is already registered in the
Lake configuration, whose default remains `Challenge`. Comparator lists
exactly seven targets, no definition exceptions and the standard three
permitted axioms. Linux verification remains pending.

The only draft correction was the import path
`Mathlib.Data.Matrix.Notation` to `Mathlib.LinearAlgebra.Matrix.Notation`.
Its original bytes and exact import-only history were archived before the
first build. No definition body, signature or numerical statement changed.

Matthew J. Colbrook retains mathematical authorship. Formalization credit is
George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA, with AI-agent
assistance; no George email is added. Original Johnson/source attribution
is preserved. Review follows the pinned Tau Ceti angles as adapted by
`docs/lean/REVIEW.md`, not an external human peer review claim.
