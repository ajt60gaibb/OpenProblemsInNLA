# Local completed-solution check — 26 September 2026

This is the preserved **pre-reorganisation** record. Its source manifest and
paths describe the former flat module layout. For the current sources, use
[the reorganisation audit](../reorganisation/README.md) and its
[old-to-new module map](../reorganisation/module-map.json). The original
manifest and captured log below have not been rewritten.

Host: macOS, arm64. Lean 4.33.1, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.

## Checks performed

From the FR-05 Lean project:

```sh
lake build Solution Challenge
lake env lean verification/final/Inspect.lean
shasum -a 256 -c verification/final/source-sha256.txt
```

The full build succeeded (3897 jobs). Existing prerequisite linter suggestions
remain. The three intentional `Challenge.lean` statement fixtures produce
`sorry` warnings, but `Solution` does not import them.

`Inspect.lean` checks the exact all-dimension quantitative theorem and original
limit, and audits their transitive axiom dependencies along with the planted
event identity, Cauchy–Schwarz comparison, and eventual bound.
`check.log` is the captured output: every audited theorem uses only
`propext`, `Classical.choice`, and `Quot.sound`.
No proof placeholders, custom axiom declarations, native decision proofs,
or unsafe declarations occur in `NLA/` or `Solution.lean`.

`source-sha256.txt` records all 177 local library modules and the
solution, challenge, comparator configuration, pinned dependency/toolchain
files, and inspection source. The original definitions in `Definitions.lean`
and `Probability.lean` are unchanged from the branch's committed versions.
Only comments changed in `Challenge.lean`; its quantitative target is now
selected in `comparator.json`.

## Scope

This is a local development check of the full bound and limit, not a run of
the repository's isolated, non-root Linux Comparator/kernel harness. The
latter requires a committed, self-contained project on a suitable Linux host.
Independent informal-statement review, provenance review, and the repository
verification workflow remain outstanding. No repository-verified status,
independent specialist endorsement, or novelty claim is made.

Earlier `proposition31/` and `proposition32/` logs are preserved historical
component checks, not fresh verification of this completed assembly.
