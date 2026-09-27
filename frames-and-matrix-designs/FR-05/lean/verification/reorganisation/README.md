# Reorganisation check — 26 September 2026

This is the historical local verification record immediately after the
subject-based reorganisation. The subsequent reusable-API refactor has its
own [current audit](../library-cleanup/README.md); the logs and source manifest
here are retained for the earlier snapshot, not for the current proof bodies.
The module map is maintained as a live migration guide: it now also records the
later 157-to-112 consolidation. Its historical hash is therefore superseded by
the manifest in the current audit, like the hashes of subsequently edited proofs.
The earlier `proposition31/`, `proposition32/`, and `final/` directories retain
their original logs and source manifests; they refer to the former flat layout.

## Structural changes

- 177 library modules became 157: 35 closely related modules were combined
  into 15, and the remaining modules were grouped by subject.
- Eight definition/entry-point modules remain at `NLA/FR05/`; implementation
  modules are in ten subject folders. `module-map.json` maps every old import
  name to its current location.
- Merged source bodies are separated by sections, keeping their local options,
  notation, and instance scopes separate. No mathematical declaration or proof
  text was changed; only imports, blank lines, and scope wrappers changed.
- Redundant imports in the public aggregation modules were removed. Their
  transitive source coverage is unchanged, modulo the module map.
- `Definitions.lean`, `Probability.lean`, `SourceParameters.lean`, `Solution.lean`,
  `Challenge.lean`, and `comparator.json` are byte-identical to the pre-move
  snapshot. The theorem names, statement boundary, and dependency pins are unchanged.
- The Lake library target now explicitly selects `NLA.FR05.+`, so
  `lake build NLA` checks all actual modules instead of requesting a nonexistent
  `NLA.lean` root module.

These properties were checked by comparing every source against a pre-move
snapshot: non-import bodies were retained, all current imports resolve to
source files, the import graph is acyclic, and the public import closure is
preserved. A backup of the original files was retained outside the repository
during the operation. The original source ZIP was not modified or removed.

## Local Lean checks

Host: macOS arm64. Lean 4.33.1, Mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474`.

```sh
lake build NLA Solution Challenge
lake env lean verification/reorganisation/Inspect.lean
shasum -a 256 -c verification/reorganisation/source-sha256.txt
```

The complete build passed (3878 jobs). Existing prerequisite linter suggestions
remain. The three intentional `Challenge.lean` placeholders remain isolated;
the solution does not import them. There are no proof placeholders, custom
axiom declarations, native decision proofs, or unsafe declarations in `NLA/`
or `Solution.lean`.

`Inspect.lean` checks the exact quantitative target and original limit and
audits the propositions, law bridges, final comparison, and final theorems.
`check.log` contains its captured output. Every audited declaration uses only
`propext`, `Classical.choice`, and `Quot.sound`.

`source-sha256.txt` records that snapshot's 157 library modules, statement/solution
entry points, comparator configuration, dependency/toolchain files, inspection
source, and module map. The pre-reorganisation manifests were not overwritten.

This remains a local development check, not independent statement review or
the repository's isolated non-root Linux Comparator/kernel verification.
The canonical problem status and permanent identifier remain unchanged.
