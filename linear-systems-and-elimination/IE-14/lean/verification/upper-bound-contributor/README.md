# IE-14 upper-bound contributor evidence

This package records the local implementation contributor's three upper-bound modules, exact source hashes, successful targeted build and kernel/axiom checks. It is not an independent referee report or a publication/CI claim.

The portable command, run from the retained IE-14 Lean project with its pinned toolchain and dependencies, is:

```bash
lake build NLA.IE14.ColumnBounds
```

`final-build.log` is the successful final build. `development-logs/` retains all 13 compiler attempts in order within each module family; earlier failures are resolved in the sealed source and are not proof evidence. The raw Lake logs/traces contain local absolute cache/runtime paths as historical provenance; they are not reproduction commands. `source/` snapshots the exact three contributed modules. `report.json` checks all ten frozen statement inputs unchanged and records full scope and the final theorem name. No repository files outside those three owned modules were edited by this proof contribution.

Packaging note: the three raw Lake JSON traces have the suffix `.trace.json` so Git retains them. Their bytes are unchanged. `original-SHA256SUMS` records the original contributor package; `SHA256SUMS` records this packaged archive.
