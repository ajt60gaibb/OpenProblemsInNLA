# Reproducing the local IE-06 proof

The package uses Lean 4.33.1, LeanCert commit
`621a43d7cf21f87872392a01e874f2f1dbddc926`, Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`, and the full dependency graph in
`lake-manifest.json`. The unchanged shared Lean/CI/Comparator infrastructure is
bound by `verification/tooling-lock.json`. Nothing has been committed, pushed,
or submitted to remote CI.

`Solution.lean` implements all six exact signatures in the independently frozen
`Challenge.lean`. Challenge is retained verbatim, including its historical
statement-phase header and six deliberate reference holes. It is never imported
by the proof library. There are no definition holes in `comparator.json`.

## Build and audit

With the pinned toolchain and dependencies available:

```sh
lake build NLA Challenge Solution KernelControl
python3 verification/check_local.py \
  --lean /absolute/path/to/lean-4.33.1/bin/lean \
  --packages /absolute/path/to/pinned/.lake/packages \
  --compare-solution --timeout 600
```

The checker copies a fresh source snapshot, verifies dependency revisions and
tracked-source cleanliness before and after the run, builds every concrete
local module, and audits every owned declaration including private auxiliary
ones. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted
transitively. LeanCert runs in kernel mode; separate rejection controls must
reject both admitted proofs and native-execution proofs. Temporary project
objects are removed after recording their hashes.

With `--compare-solution`, the same run builds the unchanged hash-locked
Comparator library and imports Challenge and Solution into separate environments.
It compares all six theorem types and recursively checks the definitions giving
them meaning, then checks the candidate proofs' transitive axioms. Exact target
coverage and an empty definition-hole list are enforced. Success is recorded
only after these comparisons and the final source/dependency stability checks.

The run uses the local Lean executable at
`/Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.tools/lean-4.33.1-darwin_aarch64/bin/lean`
and the read-only dependency cache at
`/Users/ajt253/Documents/ChrisResearch/RRF/SIMAX Version/Revision 2.2/lean/.lake/packages`.
The checker accommodates that cache's `LeanCert` directory name. These paths
are local inputs, not requirements for another machine.

Exact sources, logs, executable/dependency identities, and receipts are retained
under `verification/local/`. Consult `verification/SUMMARY.md` for the final
accepted attempt; historical attempts certify only their own snapshots.

## Comparator rejection controls

```sh
python3 verification/check_comparator_core.py \
  --lean /absolute/path/to/lean-4.33.1/bin/lean
```

This separate unchanged control checks nine assertions using the actual pinned
`Comparator.compareAt` and `Comparator.checkAxioms` APIs: matching proofs/types,
changed theorem types, changed definitions, theorem-to-axiom replacement, and
admitted/native proof rejection. Its fixtures do not prove IE-06. The
`--compare-solution` run above performs the distinct actual-theorem comparison.
Licenses and notices for the pinned tools and vendored mathematics are retained.

`KernelControl.lean` checks `log(2) < 7/10` through LeanCert's explicit kernel
router. It tests the numerical pipeline; it is not a Gaussian-growth estimate.
The mathematical proof uses symbolic Gaussian identities, inequalities, finite
unions, and limits instead of sampling or evaluating enormous cutoffs.

## Scope of local verification

Local compilation and Comparator-library execution trust the pinned existing
dependency object cache. They do not claim a clean non-root Linux sandbox,
exporter execution, or independent raw-kernel replay. The receipts record these
limits explicitly; no sandbox or acceptance gate has been replaced or relaxed.

The unchanged authoritative route remains available on supported non-root
Linux against a clean committed project, if publication is later authorized:

```sh
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh linear-systems-and-elimination/IE-06/lean /absolute/path/to/nla-lean-tools
```

It includes Landrun/Bubblewrap isolation, the exporter, raw-kernel replay,
Comparator, and rejection controls. It was not run or remotely dispatched in
this task. The maintainer's request to keep the code local is preserved.
