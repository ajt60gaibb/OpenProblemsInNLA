# IE-22 proof and verification evidence

The formalization proves the optimal eventual uniform row-deletion constant and shows that every smaller real constant fails. It also gives the squared upper bound for every positive row count and near-sharp unit-row matrix witnesses beyond every dimension and aspect-ratio threshold.

The project is copied byte for byte from the independently reviewed
campaign revision `ccc7864f5034cf7c4602f7577ceaf083ebf63d52`. Each of its 59 inputs matches
the SHA-256 map in the isolated Linux receipt. That run checked synthetic
merge `12bf4d153f725cbc326d40d694c1993d6f098eb4` and accepted these exports.

- `NLA.Proofs.IE22.uniform_squared_upper`
- `NLA.Proofs.IE22.near_sharp_unit_row_witness`
- `NLA.Proofs.IE22.target`

The run compared the frozen Challenge with the separate Solution and
accepted the exported proofs in Lean's default kernel. The LeanCert
audit checked theorem kinds, kernel trust, and the standard axiom set
`propext`, `Classical.choice`, and `Quot.sound`. The sandbox and
rejection logs record the harness controls. Mathematical source credit
belongs to Matthew J. Colbrook. The formalization and independent
reviews are credited in the project manifest and archived records.
[Archived source and package reviews](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/ccc7864f5034cf7c4602f7577ceaf083ebf63d52/docs/lean/proofs/IE-22/campaign-2026-10-23/LINUX_CI_RECEIPT.md)
· [Independent artifact audit](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/ccc7864f5034cf7c4602f7577ceaf083ebf63d52/docs/lean/proofs/IE-22/campaign-2026-10-23/linux-pr368-final/INVENTORY_REVIEW.md)
· [Original isolated Linux run](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/40324391261).

The [retained receipt](previous-linux/result.json), [Comparator log](previous-linux/comparator.log),
and [LeanCert trust and axiom log](previous-linux/leancert-proof-trust.log)
are exact copies from that run. The project uses Lean 4.33.1 and pinned
Mathlib and LeanCert revisions. See the [immutable proof package](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/ccc7864f5034cf7c4602f7577ceaf083ebf63d52/linear-systems-and-elimination/IE-22/lean)
and its Lake manifest.

To reproduce the isolated run, prepare an unprivileged Ubuntu environment
with a user systemd session and Bubblewrap as in the
[repository workflow](../../../../../.github/workflows/lean-verification.yml).
Run the pinned harness from the repository root.

```sh
tools/lean/bootstrap.sh /tmp/nla-lean-tools
tools/lean/verify.sh linear-systems-and-elimination/IE-22/lean /tmp/nla-lean-tools
```
