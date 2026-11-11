# Independent IE-22 canonical package review

**Approve canonical package commit
`06f31cdd4f76d90c7590b5582b8db4975a0055d8`, including the assembly first frozen
at `577846438f6cdb80bf237fc190021ddafd7a24a5`. No changes requested.**

Reviewer `/root/inventory`, 2026-10-25, non-author of all IE-22 proof and package
sources. This is a package/boundary/copy/preservation/provenance approval,
separate from the complete source/math approval of
`353ebcfcbbcfc08184c32f391ecb6068c7d9098f`. Independent fresh kernel replay,
actual Comparator/default-kernel/LeanCert Linux acceptance and original-artifact
receipt review remain separate gates. No promotion or Linux acceptance is
claimed here.

The portable `audit_package.py --repo ... --output ...` passes **260 checks**.
It binds all **54 actual package inputs**, **27 Lean inputs**, **23 exact shared
source copies**, all **32 original/frozen inputs**, the actual package delta and
the inspected author compiler receipt. Machine-readable hashes and checks are
in `PACKAGE_REVIEW_INVENTORY.json`.

## Exact package and proof boundary

All nineteen canonical proof modules are byte-identical to the reviewed shared
sources at `353ebcfc`, including the exact UpperParameters, UniversalUpper and
Final proofs. The other four copied inputs are the exact shared Infrastructure,
RowDeletion, IE22 statement and separately frozen Reviewed mirror. Every one
of these 23 copies matches both the immutable source checkpoint and its lock.
The shared proof sources themselves also remain unchanged.

All 27 canonical Lean inputs are unchanged from `57784643` to `06f31cdd`.
The **only** later package change is addition of
`original-scaffold/comparator.json.txt`, exactly equal to the original published
Comparator configuration. The separate audited TR-06 merge does not alter any
IE-22 package proof or configuration byte. This report does not duplicate its
independent mathematical/evidence review.

The canonical Challenge is byte-identical to the two-reviewer pre-approved
three-endpoint Challenge, SHA-256
`bd20cbb3d4495ff312192ab29fe7722463c8b74861f0a00ae83dd9b98ed4ec79`.
Comparator selects exactly:

- `NLA.Proofs.IE22.uniform_squared_upper`
- `NLA.Proofs.IE22.near_sharp_unit_row_witness`
- `NLA.Proofs.IE22.target`

There are zero replaceable definitions, and only `propext`, `Classical.choice`
and `Quot.sound` are permitted. The actual statement and model are the unchanged
published real Euclidean row-deletion definitions. Identity imports the actual
live/frozen statements and proves their Target equality by `rfl`; identity is
not substituted for the Target proof. The literal Target is actually supplied
by the reviewed Final source. Both squared companions retain their exact
approved signatures and domains.

Solution imports the actual Final proof and never imports Challenge. Its three
endpoint kernel assertions refer to the imported actual theorem constants.
The two historical helper proof bodies remain byte-preserved, with their own
kernel assertions. Definitions.lean is retained byte-for-byte and imported to
preserve those helper names. This includes its old auxiliary measurable-space
instance and extra convergence **definition**, but neither is a premise of the
new deterministic Target. The nineteen-proof/shared-statement import closure
does not import Definitions. The old Challenge's false additional convergence
**axiom** is archived only as `.txt` and is never imported or compiled as a
positive proof. The review distinguishes these definitions from an asserted
historical result.

The default targets build Challenge, Identity and Solution separately. Lake's
libraries include the actual NLA proof/statement and Reviewed modules plus
Definitions. The `.txt` archives are outside Lean source selection. Every
positive canonical Lean source is free of a Challenge import. The three
deliberate Challenge placeholders remain comparison references, not accepted
proofs. Actual placeholder rejection is a separate compiler/CI gate.

## Original preservation and permanent identity

All 32 pre-proof original inputs match the actual published base Git objects
and their committed frozen copies, including the original canonical page,
problem sources/PDF, shared/frozen definitions, complete manuscript, source
review, old project metadata and historical Lean files. Every changed old
canonical scaffold input additionally has an exact `.txt` archive in
`original-scaffold/`, now including Comparator. Current Definitions, RELATED,
old proof-review notes and direct historical logs remain unchanged where they
were retained live. The original historical Solution text is both archived and
its two actual proof bodies remain in the new Solution.

The actual canonical problem README is byte-identical to published base and
still states **Solved**. The new problem-level ORIGINAL.md is another exact
copy of that original page. The old rating/history, canonical path,
mathematical question and source attribution remain intact. All 217 permanent
ID/path pairs and the registry bytes are unchanged. There is no renumbering,
replacement mathematical target or false success count in this package.

The manuscript's original mathematical credit remains with Matthew J. Colbrook.
Metadata and prose distinguish new AI-agent formal work and independent
automated review from source-author participation and external human review.
The derivative-free covariance and qualitative finite-net implementation route
is disclosed. Neither the manuscript's explicit rate nor IE-21's quantitative
probability theorem is claimed as a formal consequence here.

## Pins, policy, metadata and evidence scope

The compiler is pinned to official Lean 4.33.1. All ten dependency records have
the same exact source URL, revision, configuration and other substantive fields
as the shared pinned manifest. The only record-field differences are the
declared **direct** Mathlib dependency: `inherited=false` and its exact commit
as inputRev, replacing the shared manifest's inherited `v4.33.1` request. The
resolved revision remains `0df444a360eaa60ab8c11dca51a86af692955474`; the Lake
file explicitly declares that exact revision. Dependency list ordering has no
source-pin effect. LeanCert remains exactly
`621a43d7cf21f87872392a01e874f2f1dbddc926`.

The first auditor incorrectly demanded byte/order equality for all manifest
records and failed this direct-dependency bookkeeping difference. That
diagnostic and driver are preserved as `INITIAL_MANIFEST_BINDING_DIAGNOSTIC.json`
and `audit_package.initial-manifest-diagnostic.py`. The corrected auditor checks
every package by name and permits **only** the two explicit Mathlib request/
inheritance differences. No mathematical source, dependency revision or
verification safeguard was changed to make the audit pass.

The metadata advertises exactly the three selected results, zero positive-proof
sorries, the standard three axioms and pending independent/Linux/Comparator
acceptance. `whole_problem_verified` is false, and the canonical page stays
Solved. Documentation honestly labels author-local builds and incomplete
acceptance gates. The actual shared verifier/workflow sources are unchanged
between the reviewed full-source checkpoint and this package commit.

I extracted the exact immutable package to a separate private directory and ran
the actual read-only metadata validator. It reports **PASS for schema and
Comparator coverage of all three declarations**. The command, validator hash
and raw output are retained in `METADATA_VALIDATION.json` and
`metadata-validation.log`. This validates metadata, not theorem truth.

The committed author-local receipt has 28 successful records for the exact 27
canonical Lean inputs plus its actual consumer. Every input hash, record source
hash and raw log matches the committed bytes. The consumer applies all three
actual endpoints to the exact live/frozen types and checks both old support
constants. Its five axiom lines contain only the standard three axioms. I read
and hash-bound this as **author macOS evidence**, not as a new independent build
or a Linux receipt. The unchanged proof/math approval, independent fresh replay
and actual CI artifact/checkout/consumer/rejection evidence have their own
scopes and must not be collapsed into this package approval.
