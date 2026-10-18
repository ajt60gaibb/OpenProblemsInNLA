# Replaying the historical SP-11 scaffold boundary

The boundary approval preceded `Solution.lean`. Its original package source
snapshots and results remain in `sp11-package-boundary-review/`.
The completed package legitimately adds Solution/default build targets and
updates its descriptive metadata. These changes do not modify the frozen
Challenge, live/reviewed statements, Identity, or Comparator selection.

To replay the original scaffold, including its historical Lake configuration:

```bash
python3 docs/lean/campaign-2026-10-17/verification/check-sp11-package-boundary.py \
  --snapshot docs/lean/campaign-2026-10-17/verification/sp11-package-boundary-review/source \
  --evidence-name sp11-package-boundary-replay
```

This invocation passed all 15 copy/lock/resolved-pin checks, six fresh positive
Lean commands and the expected seventh kernel rejection of the Challenge's
`sorryAx`. Its profile explicitly identifies historical source replay and
records that the current package now has a Solution. It does not mistake that
legitimate completed package for the absent-Solution scaffold. The original
boundary evidence and review report are not overwritten.

The current package additionally retains the original Lake file under
`reviews/boundary-scaffold-2026-10-18/lakefile.toml`. The independent
`check-sp11-canonical-copy.py` checks that historical hash and the unchanged
mathematical boundary alongside the new exact proof copies.
