# MI-06 Linux candidate packaging

Prepared 12 September 2026 after both independent final proof reviews passed.
**Actual Linux verification is pending; the canonical status remains Solved.**
No commit, push, PR, status promotion, or PDF regeneration was performed here.

The isolated branch `codex/lean-mi06-arithmetic-modulus` was fast-forwarded from
`02b807770fca860ef810cc048d6849224b8f93e1` to current upstream
`8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`. There were no tracked local edits,
no MI-06 incoming changes, and no conflicts. All nine frozen mathematical and
configuration files, all four canonical/source files, and both statement
approvals retain their recorded hashes. Both final proof reports are present.
The only new work relative to upstream is the MI-06 `lean/` project.

The project README now reports both final approvals and the remaining actual
Linux gate. The added `formalization.yaml` uses the pinned real v0.4 schema,
credits George Stepaniants's Caltech CMS formalization without email, preserves
Matthew J. Colbrook's mathematical authorship, states full original-target
scope and the excluded stronger result, and lists exactly the six Comparator
exports. `comparator.json`, the dependency pins and all proof sources are
unchanged. Existing `.gitignore` already excludes `.lake/`, `.verification/`,
`*.olean`, `*.ilean`, and `*.trace`; the Apache-2.0 license is retained.

The frozen proof handoff and reports are historical. Their pre-packaging README
was reconstructed from the reviewed text and checked byte-for-byte against its
original recorded SHA-256; it is preserved in
[source-before-packaging/README.md](source-before-packaging/README.md).
The current README supersedes only its review-status metadata. No frozen
mathematical source was reconstructed, rewritten, or changed.

[Packaging checks](packaging-checks.json) bind the nine unchanged inputs,
canonical source hashes, all four reviewer hashes and current metadata.
[Command checks](checks.json) record actual exits and logs: the v0.4 manifest
validator accepted all six declarations; the permanent-ID validator accepted
all 217 IDs against `origin/main`; both new-document whitespace checks produced
no diagnostics. Git's no-index exit 1 means an added-file difference and is
recorded explicitly, including the corrected initial diagnostic expectation.
No catalog regeneration was necessary because canonical files did not change.

The implementation build, independent fresh compilations, source correspondence,
52 standard-three axiom checks and retained kernel LeanCert inspection remain
under `../../reviews/`. These are local macOS checks at clean pinned dependencies,
not an authoritative Linux run. The shared workflow must still execute its
real sandbox, rejection controls, formal statement comparisons and default-kernel
replay for this immutable candidate before any Lean-verified promotion.
