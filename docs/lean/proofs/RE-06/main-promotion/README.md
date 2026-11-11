# RE-06 proof and verification evidence

The formalization proves the original nonadaptive matrix-query guarantee with $`C=4{,}000{,}000`$ and $`b=0`$. The fixed query program has a $`3+\varepsilon`$ error factor with probability at least $`99/100`$ under the Gaussian stream law. The proof covers zero optimal residual and rank-deficient matrices.

The project is copied byte for byte from the independently reviewed
campaign revision `5fefb820e4e7b72e45a18808d507e9b6dddc6088`. Each of its 295 inputs matches
the SHA-256 map in the isolated Linux receipt. That run checked synthetic
merge `94c6ab3fe2773767905d0de0656d3d4e4bc019aa` and accepted these exports.

- `NLA.Proofs.RE06.svd_total`
- `NLA.Proofs.RE06.query_bound`
- `NLA.Proofs.RE06.successful`
- `NLA.Proofs.RE06.original_claim`
- `NLA.Proofs.RE06.explicit_claim`
- `NLA.Proofs.RE06.target`

The run compared the frozen Challenge with the separate Solution and
accepted the exported proofs in Lean's default kernel. The LeanCert
audit checked theorem kinds, kernel trust, and the standard axiom set
`propext`, `Classical.choice`, and `Quot.sound`. The sandbox and
rejection logs record the harness controls. Mathematical source credit
belongs to Sidney Holden. The formalization and independent
reviews are credited in the project manifest and archived records.
[Archived source and package reviews](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/5fefb820e4e7b72e45a18808d507e9b6dddc6088/docs/lean/proofs/RE-06/LINUX_CI_RECEIPT.md)
· [Independent artifact audit](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/5fefb820e4e7b72e45a18808d507e9b6dddc6088/docs/lean/proofs/RE-06/campaign-2026-10-26/final-review/verification/REVIEW.md)
· [Original isolated Linux run](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/40419199614).

The [retained receipt](previous-linux/result.json), [Comparator log](previous-linux/comparator.log),
and [LeanCert trust and axiom log](previous-linux/leancert-proof-trust.log)
are exact copies from that run. The project uses Lean 4.33.1 and pinned
Mathlib and LeanCert revisions. See the [immutable proof package](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/5fefb820e4e7b72e45a18808d507e9b6dddc6088/randomized-and-low-rank-approximation/RE-06/lean)
and its Lake manifest.

To reproduce the isolated run, prepare an unprivileged Ubuntu environment
with a user systemd session and Bubblewrap as in the
[repository workflow](../../../../../.github/workflows/lean-verification.yml).
Run the pinned harness from the repository root.

```sh
tools/lean/bootstrap.sh /tmp/nla-lean-tools
tools/lean/verify.sh randomized-and-low-rank-approximation/RE-06/lean /tmp/nla-lean-tools
```
