This is an independent non-author macOS source review of exact immutable RE06 commit b8eb4d7d07dd4a682c81ba48f43ef93314fbc20b. It is support-only; no rectangular inverse-Wishart, unconditional public success/Target, Linux CI or Comparator package approval is asserted.

Run the portable source audit in a new output directory:

```bash
python3 audit_source.py --repo /absolute/repository --reuse-repo /absolute/read-only-TR04-reuse-repository --output /absolute/new-source-audit
```

Run the fresh source and rejection replay, keeping InventoryMPAudit.lean.txt adjacent to reproduce.py:

```bash
python3 reproduce.py --repo /absolute/repository --lean /absolute/lean-4.33.1/bin/lean --packages /absolute/pinned-packages --output /absolute/new-replay
```

The main repository must contain immutable commit b8eb4d7d07dd4a682c81ba48f43ef93314fbc20b and preserved authorization/base/reuse-history objects; the separate read-only reuse repository must contain 653b8f1641415f4160811648ff3e23889ba2e136. Both commands read exact Git blobs, never newer working-tree proof files. The source audit checks all 49 published inputs, 9 reuse snapshots, 103 preproof files, 217 registry entries, both actual shared TR04 files, all three phase bindings and all 33 actual source inputs. The replay uses an empty temporary project source/object directory with only the exact 33 Git blobs plus reviewer consumers/controls; it reuses the clean pinned dependency caches, not author RE06 project objects. All temporary project objects are removed, and their hashes, exact commands, sources and logs are retained in JSON/text.

The exact toolchain is official Lean 4.33.1 at 819816b2e0a3bf405af45ae5c7af2491d8f5bee6; Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 and LeanCert 621a43d7cf21f87872392a01e874f2f1dbddc926, with the complete ten-dependency pin map in the reports. Dependency source heads and clean status are checked before and after replay. This does not assert a fresh dependency rebuild.

Historical reviewer diagnostics are retained. source-audit/ is the initial failed static prerequisite assumption, corrected in source-audit-final/. diagnostics/interim-327/ records an intermediate passing static audit before the additional six actual-count/reuse checks. replay/ is the first fresh source build that rejected the reviewer-owned malformed literal-consumer syntax; it is not an accepted consumer run. replay-final/ is the new empty-project final run after whitespace-only consumer correction. Neither diagnostic required an authored-source edit.
