# IE-23 Lean statement candidate

This project is awaiting two independent statement reviews. It has eight
intentional Challenge placeholders and **no proof implementation**. The
canonical entry remains Solved; no Lean-verified status is claimed.

The complete original uniqueness conjecture is defined in
`NLA/IE23/Definitions.lean`. The proposed exact p=4 counterexample uses the
source's unchanged complex rectangular matrices, actual matrix rank and
pseudoinverse, the genuine nonzero-input supremum norm, and all complex
right-inverse competitors. See `NUMERICAL_TARGETS.md` for the exact obligations
and `SOURCE_CORRESPONDENCE.md` for attribution and the complete scope comparison.

Pins: Lean `v4.33.1`, LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`, and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, with every transitive dependency
recorded in `lake-manifest.json`. Intended checks are
`lake build NLA.IE23.Definitions Challenge`, followed by fresh separate-prefix
elaboration excluding old project objects. The eventual proof command is
`lake build Solution`; that library is registered now but remains absent until
both statement approvals. LeanCert's kernel trust audit is planned for this
entirely exact argument. No interval enclosure is required.

Actual author checks on 12 September 2026 passed three fresh commands:
Definitions, Challenge, and the compiled-declaration inspector. They found
exactly eight intended Challenge placeholders and checked all 19 definitions
with explicit LeanCert kernel trust and the standard-three axiom policy. All
ten dependency source trees were clean at their exact pins. The rational and
generic complex-polynomial reconstruction also passed.

Because the host disk was nearly full, this statement run reused the existing
private MI-22 dependency artifacts read-only. It created a fresh IE-23 object
prefix and excluded every old project object path; it did not copy or mutate
the dependencies, and it did not run a local Lake project build. The exact paths
and commands are recorded in `reviews/fresh-checks.json`. Reproduce this run
with the recorded dependency root:

```sh
NLA_IE23_DEPENDENCY_ROOT=/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages python3 reviews/check_statements.py
python3 reviews/reconstruct.py
```

With private dependencies later installed at the normal local path, omit the
environment override. Neither these author checks nor the intentional
placeholders establish proof completion or replace independent statement
review. `formalization.yaml` and the final Comparator metadata belong to the
subsequent completed-proof stage.

Analytic resolution: Matthew J. Colbrook. Underlying rational example:
Dokmanić and Gribonval, Example 4.1. Formalization: **George Stepaniants**,
**Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA**, with AI assistance. No novelty,
external human peer review, formal completion, or Linux Comparator PASS is
claimed at this stage.
