# Independent audit of the seven-module SP-11 Linux support receipt

Reviewer: `/root/lean_verification`, independent Codex AI agent, 17 October
2026. **PASS: 37 retained-evidence checks, including all 458 recorded snapshot
input hashes.** This audit did not rerun Lean or Linux isolation.

The retained run metadata identifies successful PR #361 run `39054866841`,
proof commit `e65f2892c7431202c49bf81cc09d8f5f88256343`, and merge snapshot
`95cfb5117171780bb16b93f6d7be7fe568c09e0d`. Both the statement/proof build job
`117460669321` and identity-Comparator job `117464679966` succeeded.

I decompressed and read the actual retained statement job log. Its SHA-256 is
`181e1690e0b2b77a09ac7feff551c8bf6f6b389d7c47c434b28958bb57ad8820`,
matching the receipt. Every one of the seven named SP-11 support modules has
an actual `Built` entry, and the aggregate finishes successfully with 9,006
jobs. Each of those seven source files matches both its recorded hash and its
Git contents at proof commit `e65f2892`. Their mathematical scope and local
all-export audit are separately recorded in the previous independent reports.

The actual downloaded Comparator artifact retains the passing sandbox,
raw-kernel and Comparator controls, rejected sorry/native fixtures, successful
default-kernel acceptance, and generated LeanCert kernel trust audit. Its
recorded input hashes all match current files. Its exact selected set contains
45 `identity_...` frozen-statement equalities and one `log_two_upper`
infrastructure certificate; SP-11 is selected as `identity_SP11`. No
`NLA.Proofs.SP11` result or unconditional SP-11 solution is selected. Thus the
receipt correctly distinguishes successful support-proof compilation from
isolated full-target proof verification.

Reproduce the audit offline:

```bash
python3 docs/lean/campaign-2026-10-17/verification/check-sp11-support-ci.py
```

`sp11-support-ci-independent-audit.json` retains every check, all 458 input
comparisons, and SHA-256 digests for the retained evidence files. This audit used
the retained downloaded artifacts and run metadata; it did not retrieve a new
GitHub log. Later support modules, including GreedyRelabel, MinorBasis,
GardenExpansion, and MonomialProducts, are outside this seven-module CI
snapshot. The receipt supports no full SP-11 claim or canonical status change.
