# SP-11 complete Lean source package

`Solution.lean` proves the unchanged all-graph real symmetric delta target as
`NLA.SP11.target`. For every n>0 and every simple graph on Fin n, the witness is a
real symmetric square matrix with exactly the graph's off-diagonal nonzero
pattern and nullity at least its minimum degree. Diagonals and edge signs are
unrestricted; isolated vertices, disconnected graphs and the singleton are
included. No PSD or SAP premise is imposed.

The full shared proof has passed local Lean and LeanCert kernel checks. This
canonical package contains exact byte copies of its 36 proof modules and two
statement modules; `proof-source-lock.json` records their imports and both source
and destination hashes. All 42 canonical modules passed a fresh local source build using isolated
project objects and pinned cached dependencies; the selected full export passed
LeanCert kernel trust with only the three foundational axioms. Final independent
source/scope reviews and isolated Linux Comparator verification remain pending.
The canonical problem status stays Solved and whole_problem_verified stays false.

The proof constructs the actual polynomial LSS vectors using shared variables by
original vertex label, expands their Gram entries over finite paired occurrence
colorings, and proves a unique nonzero canonical coefficient for every edge and
diagonal. Equality of shared exponent histograms gives incident-color totals by
original vertex class; label induction with actual blockers then recovers the
coloring, avoiding a separate formalization of lexicographic priorities. A
simultaneous real evaluation preserves all required nonzero entries.
Exact nonedge orthogonality, a Gram rank bound and greedy relabeling give the
original minimum-degree nullity bound. There is no assumed delta theorem,
noncancellation oracle, or extra realization hypothesis in the exported target.

The mathematical theorem and construction are due to H. Tracy Hall,
[*The Delta Theorem*, arXiv:2601.01211v1](https://arxiv.org/html/2601.01211v1).
George Stepaniants authored the retained explanatory application note. The Lean
formalization, packaging and reviews are AI-agent work; no source-author
participation or external human peer review is claimed.

The copied live statement, statement-checking infrastructure, separately frozen
statement, original canonical page and numerical specification retain their
reviewed bytes. `Identity.lean` proves live/frozen Target equality by `rfl`.
Two independent package boundary reviews approved the exact Challenge before
Solution was written; reports are under `reviews/`.
`Challenge.lean` contains one deliberate Comparator placeholder, excluded from
proof-development sorry counts. It imports only the statement. Solution's
transitive proof has no admitted result, and its kernel/axiom audit is explicit.
The numerical specification's preimplementation wording is historical.
`boundary-source-lock.json` records that earlier scaffold, including its old
boundary-only lakefile; the current complete closure is in proof-source-lock.json.
Both locks are review aids; generic verification independently hashes committed
project inputs and does not use an SP-11-specific profile.

The pinned dependencies are Lean 4.33.1, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`. After materializing dependencies, run:

```bash
lake build Challenge Identity Solution
```

At repository root, completed metadata and the real Linux verifier are checked by:

```bash
python3 tools/lean/validate_manifest.py eigenvalues-and-inverse-problems/SP-11/lean
tools/lean/bootstrap.sh /absolute/outside/projects/nla-lean-tools
tools/lean/verify.sh eigenvalues-and-inverse-problems/SP-11/lean /absolute/outside/projects/nla-lean-tools
```

The verifier requires a committed unchanged self-contained package and the normal
non-root Linux sandbox environment. It runs the real Comparator on exactly
`NLA.SP11.target`, then audits the selected theorem with pinned LeanCert kernel
trust. `comparator.json` has no replaceable definitions and permits only
`propext`, `Classical.choice`, `Quot.sound`. The actual complete local command, module hashes and logs are in
[verification/local-complete-2026-10-18/result.json](verification/local-complete-2026-10-18/result.json),
reproduced by `verification/check_package.py` with its explicit pinned dependency
cache/toolchain arguments. That script checks source/destination equality and all
ten cached dependency revisions, and rebuilds all 42 modules without shared NLA
objects. It is a direct Lean source check, not a lake build or Linux receipt. A
local build or support-only CI run is not this acceptance receipt. Preserve the actual final result, Comparator,
proof-trust and control logs before making any canonical verification claim.
Compiled objects and materialized dependencies must not be committed.
