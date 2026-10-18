# SP-11 support-module Linux CI receipt

The [pull-request run](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39054866841)
for draft [PR #361](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/361)
passed at proof revision `e65f2892c7431202c49bf81cc09d8f5f88256343`.
The CI merge snapshot is `95cfb5117171780bb16b93f6d7be7fe568c09e0d`.

The [statement/proof build job](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39054866841/job/117460669321)
actually built each of the seven SP-11 modules. Their source-level LeanCert
kernel assertions passed; the displayed transitive axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`. The aggregate completed 9,006
Lake jobs. The separate local all-export audit records 57 constants and all 35
actual theorem exports, checking theorem kind, kernel trust, and axiom closure.

The [isolated Comparator job](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39054866841/job/117464679966)
passed its real sandbox/kernel/rejection controls and returned
`comparator-accepted`, with LeanCert proof trust `kernel-checked`. Its selected
scope is **45 frozen-statement identities and one numerical infrastructure
control**. This checks the SP-11 statement identity among the other identities.
It does **not** compare an unconditional SP-11 solution: no such proof exists.
The separate canonical-project verifier selected no changed problem project;
its skipped `verify` job is not additional SP-11 proof evidence.

The [retained machine-readable receipt](../../campaign-2026-10-17/verification/sp11-linux-ci/receipt.json)
binds all seven proof source hashes, every recorded Comparator input hash,
actual run metadata, the downloaded Comparator artifact, and the compressed
full statement-job log. All recorded snapshot input hashes match the current
source. The uncompressed job-log SHA-256 is
`181e1690e0b2b77a09ac7feff551c8bf6f6b389d7c47c434b28958bb57ad8820`.
This is support-proof CI evidence, not a full SP-11 verification or status
promotion. Shared-variable non-cancellation, greedy-order transport and final
unconditional assembly remain the next mathematical gates.
