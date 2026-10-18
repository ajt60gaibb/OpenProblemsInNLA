# SP-12 canonical package boundary — independent approval

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
I did not author the SP-12 statement definitions or canonical scaffold.
**Verdict: approve this exact frozen boundary for subsequent proof packaging.**
This approval does not assert a proof of Target or Linux acceptance.

| File | Reviewed SHA-256 |
| --- | --- |
| `NLA/Statements/SP12.lean` | `c41acae980a06e3f1e8d59e2c552f85812c521ed5e66473b74e01542bfd80f2b` |
| `NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `Reviewed/SP12.lean` | `adfb89f439ce5e2959aaeeb4b3ef6c432bf38f364567765715fdd8f9a1510d86` |
| `Challenge.lean` | `cd63c947c028b797e2ec3a9b82807d1a89d81b1283b25d6c814643a278480941` |
| `Identity.lean` | `4e1bee861377406ce94b1c4e836a6e832551c501afec95866554b081358cf82a` |
| `comparator.json` | `c8cf6cf64580f9706da94d07ced6b72eaad111c889f77074fd8c70befd7bd6bd` |
| `lakefile.toml` | `dfaf47e16e29b6c21af643cc609b2a81706448d9141cfd8d24cd9a45e627f74c` |
| `lake-manifest.json` | `1986396d34bc6c5912031cf620ae3989dd2964e70277e33e2b09aa5703066afe` |

Package: `eigenvalues-and-inverse-problems/SP-12/lean`. Its live statement,
infrastructure, frozen reviewed statement, original canonical source,
numerical specification, license and toolchain are exact source-lock copies.
The original canonical page has SHA-256
`cdc8003bc5160604408ce6b95c344a4ea1b9bfbf8af0f99ae1e8e016648d53e1`.

The exact conclusion is one real symmetric matrix for every positive-order
finite simple graph, simultaneously satisfying the off-diagonal edge/nonzero
equivalence, PSD, full SAP and nullity at least the chromatic number minus one.
The explicit double quadratic sum is real PSD together with symmetry. SAP
quantifies every real symmetric test matrix and retains all three distinct
constraints: ordinary `A * X = 0`, pointwise Hadamard products zero, and zero
diagonal. It does not replace either Hadamard equation with ordinary matrix
multiplication. The chromatic number is the attained least natural count of
proper `Fin` colorings; the identity coloring makes that set nonempty. For
positive order it is positive, so natural subtraction by one is the intended
difference. Real finite matrix rank is bounded by the order, giving the usual
nullity. This is the original witness formulation of the displayed nu bound.
Disconnected graphs, isolated vertices and order one remain included.

Challenge contains exactly the deliberate comparison theorem
`NLA.SP12.target : NLA.Statements.SP12.Target`. Comparator selects that one
theorem from future Solution, with no definition holes and only `propext`,
`Classical.choice`, `Quot.sound` permitted. Identity proves the live/frozen
proposition equality by `rfl`. Neither that equality nor compiling the
Challenge placeholder is a proof of Target.

Fresh isolated-source verification passed all **15 source-lock/copy/resolved
dependency checks**, then **six positive Lean commands** for Infrastructure,
live SP12, Reviewed SP12, Challenge, Identity and an independent consumer. The
consumer checks the selected name is a theorem constant, prints its exact
type and audits Identity in kernel mode. A seventh command deliberately
audits Challenge in kernel mode and **rejects `sorryAx`**, as required.
All ten dependency repositories match the pinned revisions and have clean
tracked sources. All frozen package bytes were unchanged and Solution was
absent throughout the review.

```bash
python3 docs/lean/proofs/SP-12/verification/check-boundary.py
```

Exact snapshots, generated consumers, raw logs, compiler identity and
machine-readable result are in `verification/boundary-review/`. The build
uses fresh private project objects and pinned cached dependency objects.
The two prior shared-boundary approvals are retained separately. This is
independent AI-agent review and local macOS kernel evidence, not external
human review, a complete SP-12 proof or Linux Comparator evidence. The
completed Solution and its actual source closure require separate review and
real Linux verification when available. No canonical or proof source was
modified for this review.
