# TR-14 exact complex root data: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen root-data module for aggregate import. This is the first factorization gate toward CRT; it does not supply a quotient algebra equivalence, local moment functional, or tensor-width theorem.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/TR14/LocalCRTRootData.lean` | `96d8d86b6e15c024978d44b78aa525dc0cbb1231fd09d274c1c0c32242c9a263` |
| Exact CRT transfer contract | `d267bd05e2f9ce15bc5c76c6614e6ce66f627b6e1f6a1c235eebcb06ddbcf184` |
| Independent mathematical pre-review | `48941cc712607f82f2bcf560dd287d25f1ec92afd5246ce557bd33f59388ef00` |
| Separate imported audit `/private/tmp/tr14-local-crt-root-data-independent-audit.lean` | `c3dd43c04104876b6afd30c5a2f1257d4dcb1e47198676df3d8de66d373ab46c` |

The source uses `g.roots.toFinset` as the distinct root index and `g.roots.count α` as its multiplicity. Membership gives each indexed root positive multiplicity. Summing counts over the support gives exactly `g.natDegree`; no simple-root assumption is made. For monic `g`, the full multiset factorization groups to `g = ∏α (X − C α) ^ ℓα`. Distinct indices have distinct values, so the corresponding linear factors and all their powers are pairwise coprime. The positive-degree case gives a nonempty support. These claims match the first boundary of the approved root-factorization contract, including repeated roots and arbitrary multiplicities.

The pinned Lean 4.33.1 direct module build passed 3,423 jobs. My separate imported LeanCert audit exited zero, checked all five public theorem signatures, reran `#assert_trust kernel`, and printed only `[propext, Classical.choice, Quot.sound]`. The source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

The algebra CRT equivalence, its root-image identity, supported local functionals, all-moment reconstruction, projective-root multiplicity correspondence, and the complete TR-14 Target remain open.
