# Independent verification recovery — 23 October 2026

This directory records recovery from the original independent verifier's actual session log after its temporary workspaces disappeared. The source log hash and exact line locations are in `recovery-provenance.json`. Historical calls and Python fragments are inert `.txt` files; no historical shell/network/destructive command was executed to recover them.

Fourteen historical audit drivers were reconstructed with restricted static evaluation of string/path construction and literal replacements. Their exact provenance is in `statically-reconstructed-driver-provenance.json`. They preserve their historical runtime paths. Nine literal historical review prose files are retained under `historical-reports/` as `.md.txt`, with extraction provenance. Other reports/approvals that depended on lost dynamic result files remain only as their actual generator fragments. Four complete literal historical source locks and one explicitly partial literal lock are preserved under `historical-locks/`, with `historical-lock-provenance.json` recording the exact construction fragments. No missing historical result, command log or PASS approval has been synthesized. The later exact correction to the controlled-atlas report was applied from its recorded literal replacement, with the earlier wording retained separately.

The last historical controlled graph derivative, normalized graph weighted-area and actual graph-character/projection aggregate audits had not produced observed terminal results before interruption. They require fresh audits. Historical report prose and author recollections do not substitute for those new results.

`historical-literal-source-hash-expectations.json` preserves 37 independently recorded module hash expectations. `fresh-preservation-before-kernel-audit.json` freshly checks those 37 source hashes; all 217 canonical README paths and bytes and the registry against exact promoted PF-05 commit c4c7be59; the intrinsic TR-06 statement against published 36767fa4; and the original TR-06 TeX/PDF bytes. These byte checks pass and preserve the original mathematical targets.

A separate current-runtime driver, `../check-recovered-support-2026-10-23.py`, freezes all 70 selected recovered/new support modules and their complete local import closure before using isolated output objects. The 70-source lock is `../recovered-support-70-source-lock-2026-10-23.json`, and the exact invocation is `fresh-audit-invocation.json`. Fresh evidence goes in `../recovered-support-70-review-2026-10-23/`; only that directory's actual completed result can establish the new kernel audit. This support audit excludes unfinished final assembly and makes no full intrinsic TR-06 Target, actual uniform graph-fiber, finite actual normalized-graph volume or authoritative Linux Comparator claim.

Reproduce the full selected checkpoint with a new evidence directory:

```sh
python3 docs/lean/proofs/TR-06/campaign-2026-10-18/verification/replay-recovered-support-2026-10-23.py \
  --lean /absolute/path/to/lean-4.33.1/bin/lean \
  --packages /absolute/path/to/pinned/.lake/packages \
  --evidence-name fresh-support-replay
```

The launcher derives all 70 complete module names from the frozen lock. The driver records compiler identity, every actual dependency revision/cleanliness check, exact frozen inputs, generated consumer, all compile commands/logs and post-build preservation. It refuses to overwrite existing evidence.
