# RA-10 isolated Linux proof receipt

The [RA-10 verification job](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/38902736024/job/116978870284)
on draft PR #359 passed on 16 October 2026. It checked branch head
`14a35c1716049c3ec19832540cc5116c2de433e0` through GitHub's PR merge
commit `f1fae49a506126bb7d3b99eae6a10e760fd65861`. The uploaded artifact
is `lean-RA-10`.

Comparator selected only `NLA.RA10.target`, whose challenge is the complete
frozen `NLA.ReviewedStatements.RA10.Target`. `Identity.lean` proves by `rfl`
that the frozen and live target propositions agree. The Solution applies the
full theorem from pinned `lean-statements` revision
`844237f7e979146c937c0dc88f5c3f6e5f40c9b9`, using universal constant 11.
Comparator rebuilt the project in isolation, accepted the solution with Lean's
default kernel, and printed `Your solution is okay!` after 3,048 jobs. The
generated LeanCert proof-trust audit required the selected export to be a
theorem constant and passed `#assert_trust kernel`. It reported only
`propext`, `Classical.choice`, and `Quot.sound`; there was no `sorryAx`, native
execution axiom, or custom axiom in the selected proof closure. `result.json`
records `result = comparator-accepted` and
`lean_cert_proof_trust = kernel-checked`.

The exact input hashes in `result.json` include:

| Input | SHA-256 |
| --- | --- |
| `Challenge.lean` | `e6e5a0b18e6427f12cdf267291b82f7df4f255aac96bc8cdac7f034a52c33af2` |
| `Identity.lean` | `e439017f98431648833a497da9c8340bde8cb4b86d9170a338cdeb0e38472617` |
| `Solution.lean` | `c596533c2d1a83d1facfc398c6afa9d2b78423ef112bd9030ad60117beb7ee70` |
| `comparator.json` | `dc975d9412cbc151a572f898ce585d46e9e7b8e5be895501fc352b33ae0ca6c5` |
| `lake-manifest.json` | `d03ac591181fc3122badad6a5c47a45ed1f5e994eea9e9fc990cb30ed85a5145` |
| `source-lock.json` | `e598473d9f4445c5f130d989a4a1b627d9aed55638b0856238151b2aaad87602` |

The shared verifier source-lock SHA-256 was
`b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`;
the generated LeanCert proof-trust source SHA-256 was
`39ede64ddb6fcc0dbf09492d96be939445a1ab098fc517a21425536b244ad738`.
SHA-256 of the downloaded artifact's key files:

| File within `lean-RA-10` | SHA-256 |
| --- | --- |
| `result.json` | `371bee5b898e336a99797fa38d55233ac244f9c7e0ac64a3d56abcce827e2be5` |
| `comparator.log` | `4ec6738610c55ee4e6c6de44fb47e47f5a0712b3c4b8e0f46af16cc3aa019339` |
| `leancert-proof-trust.log` | `c0ee72bd9f71a8a1236c10d4ff9651896b658dd6d28e84ef35f75677612aef79` |

The two independent AI-agent [final source reviews](../../../../randomized-and-low-rank-approximation/RA-10/lean/reviews/FINAL_FORMALIZATION_REVIEW_1.md)
and [second review](../../../../randomized-and-low-rank-approximation/RA-10/lean/reviews/FINAL_FORMALIZATION_REVIEW_2.md)
bind the original statement, exact wrapper bytes, numerical constant, and the
95-module pinned proof import closure. This receipt is mechanical proof
verification for RA-10; the reviewers separately assess mathematical fidelity.
