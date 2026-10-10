# TR-14 normalized middle catalecticant rank: independent Lean review

**Reviewer:** `/root` (AI agent), 10 October 2026. **Verdict:** APPROVE frozen `MiddleCatalecticant.lean` for the exact middle Hankel rank theorem in a normalized monic chart. This does not establish the original-coordinate rank theorem or `NLA.Statements.TR14.Target`.

I read the complete source and compared its elaborated public statement with the independently reviewed mathematical contract. `middleCatalecticant h` has exactly `⌊D/2⌋+1` rows and `⌈D/2⌉+1` columns, with entry `h_{i+j}` and a proof that every accessed index is at most `D`. The theorem retains a nonzero moment vector, positive exact monic apolar degree `r₀≤D`, the middle-degree bound `r₀≤⌊D/2⌋+1`, and vanishing of every lower apolar kernel. It proves `Matrix.rank C_h=r₀` without squarefree, generic, or numerical assumptions.

The source constructs both truncated power-to-quotient maps and proves each is surjective because its domain contains the full power basis through `r₀−1`. It makes the row pairing map injective using the independently reviewed Frobenius theorem. The all-moment quotient equality then gives the exact `mulVecLin` factorization of the rectangular Hankel matrix through these maps. Surjectivity and injectivity establish the rank. This covers balanced and odd middle splits, including `D=1,r₀=1`. No `GL₂` transport is claimed; in particular the source does not infer original-coordinate least apolar degree from matrix-rank invariance alone.

I separately imported the frozen module under pinned Lean 4.33.1, checked both public signatures, ran LeanCert `#assert_trust kernel`, and printed the transitive axioms. The audit exited 0 and reports only `propext`, `Classical.choice`, and `Quot.sound`. A source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/TR14/MiddleCatalecticant.lean`** | **`2ddbf89822f72c4cbc5a2cd6935adbbab49239476943275ac4a5b2853be9d8a1`** |
| Approved `MIDDLE_CATALECTICANT_PRE_REVIEW.md` | `b72a9a0e25358fbe2b41dff423c638c03202bc367d6153cf4f08c0e1fb054981` |
| Independent mathematical pre-review | `ae61fa9d9216360f379f5747eb92a0210abdc6a872b0b97f67cd96a47ce9d954` |
| Imported `/private/tmp/tr14-middle-independent-audit.lean` | `6bc320ac6248192dcb0435a14ee1133462d74bf1e3f846995225f68b3aa22a0f` |

Changed source or contract bytes reopen this review.
