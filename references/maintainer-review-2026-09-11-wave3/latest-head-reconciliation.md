# Branch updates received during final publication

The six contributor branches incorporated published `87366c62` while the earlier complete integration `8f01be1` was undergoing its required check. Their original proofs remain unchanged. Three independent delta reviews verify all new hashes, provenance records, preserved upstream content and the complete mathematical/PDF continuity:

| PR | Latest reviewed head | Delta report | Disposition at this integration |
| --- | --- | --- | --- |
| #68 | `24ea75aa75b44b280c7aa0a342ea900f0fdd7be4` | [AA-01/discrepancy and rook pivoting](audit-latest/PR68-83-delta.md) | Included; required check passed. |
| #83 | `9b35b5e246989843cd67b2fed702216ea1f0acdb` | [AA-01/discrepancy and rook pivoting](audit-latest/PR68-83-delta.md) | Included; required check passed. |
| #85 | `1f9a8bbd7cce9ae429fd7fd17ff409da751c414d` | [MI-28 and MI-24](audit-latest/PR85-91-delta.md) | Included; required check passed. |
| #91 | `5d5f2a32a17c0ed7bb9fdfc976ab7af44c19dd4f` | [MI-28 and MI-24](audit-latest/PR85-91-delta.md) | Included; required check passed. |
| #93 | `d9e25009e3ce65cf864002354830bdcc286f7252` | [RA-12 and RA-10](audit-latest/PR93-103-delta.md) | Mathematical PASS; this replacement head remains outside integration pending its replacement workflow approval. |
| #103 | `494438ee01cde9ad5706537b026d85b9aab03b1b` | [RA-12 and RA-10](audit-latest/PR93-103-delta.md) | Included; required check passed. |

The previously reviewed and explicitly workflow-approved PR93 commit `c797aee814c8bebe4452329c93f5d84fd9c41f1f` is already an ancestor of the original six-PR integration. Its complete RA-12 proof and solved catalog entry are present. The refreshed PR93 head adds upstream integration provenance but no proof change; its replacement required run `34657927827` was held pending separate user approval. The refreshed head and its new provenance files have **not** been included or indirectly executed through the review branch. Consequently the current GitHub PR93 remains open at this publication even though its originally reviewed mathematical contribution is included.

The five accepted replacement heads are ordinary merge ancestors of `5da9170b489d006e0ea1bbfd784b4a433db8a16b`. The [merge records](latest-integration.jsonl) show their complete added paths. Compared with `8f01be1`, only 18 reference/provenance files change; every canonical README, original target, proof source/PDF, ID registry, validator, test and required workflow remains unchanged. The combined AA-01 canonical presentation and its two-page PDF QA are therefore preserved. The root validator and all 17 numbering tests pass again.

The older Colbrook transfer reference summary now explicitly labels RA-10's partial result and RA-12's auxiliary examples as historical and links the later complete proofs. Their original authored manuscripts, reviews and attributions are unchanged. RESOLVED.md already contains the corresponding historical clarifications. RA-13 belongs to the continuing task's separate review and is not silently marked solved here.

At this point 17 current PR heads are accepted for closure, with PR93's replacement head still pending. Eighteen reviewed mathematical submissions contribute to the retained catalog. The catalog counts remain **203 entries: 67 solved, 65 open, 70 partially resolved, one solution claimed**. The newer audit task owns the continuing submissions and will receive the exact published integration state and outstanding PR93 gate.
