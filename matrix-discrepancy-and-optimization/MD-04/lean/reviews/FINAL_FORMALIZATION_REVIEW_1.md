# MD-04 independent statement and proof review

**Phase:** Final formalization, first independent referee. **Reviewer:** OpenAI Codex agent `/root/md04_independent_audit`, 16 October 2026. **Verdict:** APPROVE the exact published MD-04 target and its Lean proof at the source hashes below. The reviewed proof was already merged in PR #354; I inspected it at `origin/main` commit `47006df8b3a6c724a557266c891893d03e69323a`, and all 31 project input hashes matched the successful CI artifact for PR merge commit `4b5be52826d24d0e640862cf1a5a5620cc8d0312`. This reviewer did not implement the proof or change its Lean source. This is an independent AI source review, not external human peer review. A second independent final-formalization review remains required by `docs/lean/REVIEW.md` before this proposed status promotion is final.

## Exact target

The canonical [MD-04 README](../../README.md) asks for one finite real constant `C > 0` before every positive `m,n`, integer sparsity `1 ≤ t ≤ m`, and every `m × n` matrix with entries in `{0,1}`. Each complete column sum is at most `t`; one signing assigns `-1` or `1` to every column; every row has absolute signed sum at most `C √t`. This includes `t = 1`, `t = m`, zero columns, and all incidence patterns. The source is an offline existence statement and requires no algorithm. The original canonical bytes are preserved in `docs/lean/statements/MD-04/ORIGINAL.md` (SHA-256 `a8be36a5217cb0b3031c8f87cfc25e5421ca78dd8c42ecc151219fa62eb8156e`). The status and evidence additions to the live README do not change that mathematical question.

`NLA.Statements.MD04.Target` has precisely those quantifiers and weak inequalities. Its real `Fin` matrix, full finite sums, rowwise absolute values, and `Real.sqrt` express the source matrix and infinity norm. The source and copied target have identical SHA-256 `c3536d295078f8223c82046f80f2d4a02eee5310cd07125013d303991ae41894`; the reviewed copy has SHA-256 `e7893db1c2656e6834009267738b6244c1b0e60dde582a525b0009ae079c7257`. `Identity.lean` checks their definitional equality.

## Proof and numerical fidelity

The [reduction](../NLA/MD04/Reduction.lean) proves `NLA.Statements.MD03.Target → NLA.Statements.MD04.Target`. For a `{0,1}` matrix `A`, every `A i j ^ 2 = A i j`. Because `t ≥ 1`, `Real.sqrt t > 0`; hence `B = A / Real.sqrt t` has each squared column sum at most one. The MD-03 theorem supplies a single signing for all `n` columns and an absolute row bound `C`. Multiplying by the positive `Real.sqrt t` gives exactly the MD-04 bound `C * Real.sqrt t`, simultaneously for all rows. The reduction does not use `t ≤ m`, which is permissible because it proves a stronger implication; it does not remove that condition from the target.

The [MD-03 bridge](../NLA/MD03/Proof.lean) is byte-identical to the MD-03 project's bridge. It obtains `C = 36` from Gabriel Dahia's pinned formalization of the Komlós theorem and translates its discrepancy predicate into explicit signs and row sums. The final [MD-04 theorem](../NLA/MD04/Proof.lean) applies that theorem to the reduction. The published MD-04 resolution quotes the sharper `3 √(2π)` bound of Guo, Fang and Lu; the original target asks only for an existential universal `C`, so `36` proves the complete original target without changing its numerical requirement. Mathematical attribution to the published resolution and Stepaniants application note remains in the canonical page.

The [Challenge](../Challenge.lean) states exactly `NLA.MD04.target : NLA.Statements.MD04.Target`; its deliberate `sorry` is a comparison hole and is not imported by the [Solution](../Solution.lean). `comparator.json` selects that one theorem. There is no `sorry`, `admit`, custom `axiom`, or `unsafe` declaration in the proof path. The [isolated Linux receipt](../../../../docs/lean/proofs/MD-04/LINUX_CI_RECEIPT.md) binds the exact source hashes, verifies the Challenge and Solution with the default Lean kernel, and reports only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms.

| Reviewed input | SHA-256 |
| --- | --- |
| `NLA/MD03/Proof.lean` | `3e38a245007e2b860adacd97b89046d49b90f0f8e681dd5db43cafef6e97e93c` |
| `NLA/MD04/Reduction.lean` | `d05b5b76206215f4c63d400f85a2dd70a40718a71fcb406c033937b7f88525e2` |
| `NLA/MD04/Proof.lean` | `e6510ed6ee38cc9407b5babae4e13db85dce9139f0abb4478ec44ce7a3b2ce91` |
| `Challenge.lean` | `b62b97989a48f9d3936cad7a41b20a899d99692b449d7d421bc1413603f39260` |
| `Solution.lean` | `9cd9c0c8ae1d0789800951e731b44ef75aca007a34484f4047e991c00d121531` |
| `comparator.json` | `a456d61c696bc42a45d1f388290b8d9ed50d0a97406b98bfe953e4af83583f70` |

**Responsibilities covered:** fidelity and scope, proof correctness and quality, and reuse/documentation/attribution. I inspected the source and the downloaded CI artifact's `result.json`, `comparator.log`, and kernel controls; I did not rerun Lean locally. The successful kernel and Comparator execution is recorded separately in the linked CI receipt. Neither record claims an external human audit of the substantive Komlós library or the historical Guo–Fang–Lu manuscript. This first review alone does not satisfy the repository's two-referee requirement.
