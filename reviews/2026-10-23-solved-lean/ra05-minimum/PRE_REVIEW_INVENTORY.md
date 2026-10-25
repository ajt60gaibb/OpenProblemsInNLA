# Independent RA-05 minimum-support pre-proof review

Reviewer: OpenAI Codex AI agent `/root/inventory`, 23 October 2026.
Author of the reviewed packet: `/root`. I did not author its contract,
Challenge signatures, RA-05 definitions, or mathematical source.

**PASS for implementation of these eight support lemmas.** This is a semantic
and mathematical pre-proof review, not a Lean elaboration result, proof review,
Comparator acceptance, CI receipt or proof of RA-05. The full target remains
`Classification ∧ NegativeAnswer`; none of these eight lemmas establishes its
joint asymptotic classification, lower bounds or negative additive answer.

## Frozen inputs

Published sources below were read directly from commit
`5487945e5a72abd952b0c89915915de8cc9b3e65`. SHA-256:

| Input | SHA-256 |
| --- | --- |
| `CONTRACT.md` | `5055ea71b579eb464da47fced1ca95b7967b57e8694b948c65d62b487b0e94cc` |
| `Challenge.lean` | `6bf0be68c5353fb3d20e48ae6b46fc9b601646309bafa70612708c7d84fcf5f0` |
| `randomized-and-low-rank-approximation/RA-05/README.md` | `6e03461d0079b656779e5b87d5faa91f198c4c90ea63beb613732226e678181c` |
| `docs/lean/statements/RA-05/ORIGINAL.md` | `6e03461d0079b656779e5b87d5faa91f198c4c90ea63beb613732226e678181c` |
| `docs/lean/statements/RA-05/NUMERICAL_TARGETS.md` | `23a9cb637b7b1456fe0a0f06f3ee414c3c7dbcfc5c80a69fc303b7e347166ac5` |
| `lean-statements/NLA/Statements/RA05.lean` | `3438fe4ca2bcf313f3336c94f6a2105b83ee918b5d266009efc0c4f76c121e1e` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |

The canonical page and preserved ORIGINAL are byte-identical. The packet imports
the actual RA-05 definitions without introducing a replacement cost, coreset,
minimum or supremum. It proposes a distinct support namespace and no change to
the canonical ID, path, status, original mathematical question or frozen Target.

## Review of the exact signatures

| Export | Assessment |
| --- | --- |
| `rowCost_nonneg` | Correct for every real `p`: its base is `Real.sqrt` of a sum of squares, hence nonnegative; Lean's totalized real power preserves that nonnegativity. No positivity or projector premise is needed. |
| `cost_nonneg` | Correct finite sum of the previous actual row costs. |
| `strongCoreset_one` | Correct under `0 ≤ ε`. The actual nonnegative weights are one and the weighted cost equals the unweighted cost for every admissible projector simultaneously. Both inequalities follow from cost nonnegativity and `ε * Cost ≥ 0`. The proof must not specialize to one subspace. |
| `supportSize_one` | Correct: every element of `Fin n` has nonzero weight, so the filtered universe has cardinality `n`, including `n = 0`. |
| `minimumSupport_le_support` | Correct without any accuracy premise: the supplied actual coreset itself makes its support cardinality a member of the natural budget set. Its natural infimum is at most that member. No minimizer is assumed. |
| `minimumSupport_attained` | Correct under `0 ≤ ε`: unit weights make the budget set nonempty, so its natural infimum is a member. Its witness has support at most that infimum; the preceding lemma gives the opposite inequality, yielding exact equality. This is a natural least-element argument, not an unjustified assertion that an arbitrary real infimum is attained. |
| `minimumSupport_le_rowCount` | Correct by the actual unit-weight coreset and its exact support cardinality. |
| `minimumSupport_le_worstSupport` | Correct with only `k < d`: the dimensions and matrix appearing in the statement supply a literal member of the set defining the ENNReal supremum. Completeness of ENNReal gives the bound. This membership is true even outside the coreset domain, since `MinimumSupport` remains a total natural value; it does not assert attainment, feasibility or finiteness of `WorstSupport` there. |

The broad support domain properly contains `p > 2`, `k ≥ 1`, `0 < ε < 1/2`
from the retained target. Empty rows, zero columns and `k ≥ d` do not invalidate
the first seven statements. The eighth keeps the exact `k < d` restriction from
the supremum definition. No argument changes row weights into replacement
vectors, permits negative weights, changes the support count, assumes input
rank, restricts the projector family, or requires a common bound on dimensions.

The eight Challenge holes are intentional reference placeholders and are not
proofs. Implementation approval applies only to these exact hashed statements.
Final source review must inspect actual proof imports, LeanCert kernel checks,
transitive permitted-axiom output and reproducible logs, and must continue to
label this result as support rather than a complete solution of RA-05. No
numerical certificate is needed for these order and finite-set facts.
