# FR-05 isolated Linux proof receipt

The [FR-05 verification job](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/38000947893/job/114058782811)
on draft PR #342 passed on 9 October 2026. The workflow checked a fresh
snapshot of the committed project inside its restricted Linux user service.
The job's uploaded artifact is named `lean-FR-05`. The snapshot receipt
identifies repository merge commit
`e70f6976c51d4ef1246b395aeb0ff0678b9483e1` (PR head
`1d262c8609a6ba3cfd85989fa8ac1317a04fec93`).

Comparator rebuilt the Challenge and Solution in isolation, checked the
Solution against the challenge holes with Lean's default kernel, and printed
`Your solution is okay!`. The subsequent generated proof audit built the
reviewed LeanCert verification module, required each selected Solution export
to be a theorem constant, and passed `#assert_trust kernel` on all four
selected declarations. Both final FR-05 conclusions were among them:
`phaseRetrieval_injective_probability_le_inv` and
`phaseRetrieval_injective_probability_tendsto_zero`. Every transitive axiom
report was exactly `[propext, Classical.choice, Quot.sound]`; there was no
`sorryAx`, native execution axiom, or custom axiom. The receipt records
`result = comparator-accepted` and
`lean_cert_proof_trust = kernel-checked`.

The audit source SHA-256 in `result.json` is
`dec42c351a57f49c419b9a1ca287de0102bd26e3131c5e9e8d39942886b910de`.
SHA-256 of the downloaded artifact's key files:

| File within `lean-FR-05` | SHA-256 |
| --- | --- |
| `result.json` | `1c03d6c13f4c0ef0928505b325852b952132874d1f3ef563479ad9ae76805a42` |
| `comparator.log` | `2d0c715b8ddc419c680e77d5b2256ae8b0d529c89d50163b724d7048754ffd3b` |
| `leancert-build.log` | `48995815911f2e31bfdb7244f0e6b0236ea32f22b6933c28f95ccd41283d481f` |
| `leancert-proof-trust.log` | `c3bc7b688b6e7247d717ae1a0ff579a156571398665ba05d4a3d34d76ff1f5f0` |

The separate [independent mathematical statement and proof-chain review](INDEPENDENT_REVIEW.md)
binds the original problem and local source files. This receipt is a proof
verification result for FR-05; it makes no claim for other problems.
