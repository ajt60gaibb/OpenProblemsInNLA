# FR-12 Linux candidate handoff — 2026-09-12

**PASS for candidate metadata and preservation; actual Linux verification remains pending.** The completed seven-export proof has both independent statement and final approvals. The current README and actual v0.4 manifest accurately report the local checks and pending Linux Comparator/default-kernel and operational gates. Canonical FR-12 remains **Solved**. No commit, push, PR, canonical page, PDF, index, proof or configuration was changed by this packaging step.

The archive [frozen-statement-stage-README.md](frozen-statement-stage-README.md) is byte-identical to the reviewed README at SHA256 `74bde55ac0c513f8cbfd84856775e9c1bf79bf8cf9bbe4843f3d0e942c7df76a`. The 74-file proof freeze is unchanged at `c65d4deaa3e02af8c20a584dd81b944dbdc72f262e326630e115e5fc9070aa87`. Only the current README differs among those 74 files; **all other 73 and all four original sources are unchanged**, including all mathematical definitions/proofs, Challenge, numerical targets, source map, Comparator configuration and toolchain/dependency pins. All 217 canonical pages and the append-only registry remain identical to the pre-packaging worktree.

Both independent statement reports and final reports remain byte-identical:

| Review | SHA256 |
| --- | --- |
| Statement referee 1 | `1f5dacc0d57302b09a2c25c71372c1527d01b3f0b247a9183b1130e4a45fd2fe` |
| Statement referee 2 | `d288c647cedf362609a2630c8072ba66331e04d572ca11632cf6065110581e54` |
| Final referee 1 | `b0f455ab34b6d79a0f7fd5c9560a5e1b67eb4bf4a2a6d85772d87e6549428d6f` |
| Final referee 2 | `253962587f197745f234aec95b4a3570b3f4f0e4d55feb37bdca6372d62490a9` |

The formal recurrence is **m! H(m)² ≤ H(2m)**. The stronger informal all-matching recurrence with factor (2m−1)!! remains outside the seven exports. The exact source lower bound and complete original all-positive-real-C conjecture negation are fully in scope. LeanCert performs actual kernel trust auditing of the exact proof; no numerical interval certificate is claimed. George Stepaniants's name and full Caltech Computing and Mathematical Sciences department affiliation are visible, with substantial AI assistance and original Ferber–Jain–Zhao credit; no email is added.

The actual vendored v0.4 schema and Comparator coverage validator passed for all seven selected exports. The original Comparator configuration permits only `propext`, `Classical.choice`, and `Quot.sound`, with no definition exceptions. Both permanent-ID validators (`origin/main` and `nla-upstream/main`) and all 17 permanent-ID tests passed. All ten dependency Git trees remain clean and equal to their exact manifest revisions. The prior fresh author/referee proofs were not unnecessarily rebuilt for metadata edits; these metadata checks are not a Linux execution claim.

- Current project README SHA256: `b28c59332646f8c84ab5f156aedfa6afec97ad1cab73957cb9443d8b16d43a11`.
- Current `formalization.yaml` SHA256: `fc22b276320f4fabb66fcea03ddc08a546482ffaefbc9292df9c1f42a2baab74`.
- Full [packaging record](packaging-record.json) SHA256: `6d8c08f5bba644c3ec36bfc16b862902bb89f5236cf542911a5bf9e50792287c`.
- [Checks and raw logs](checks.json), [dependency identities](dependency-check.json), and [preservation driver](check_packaging.py) are retained here.

The outer `EVIDENCE-MANIFEST.json` binds every evidence file in this directory except its own exact path. It does not exclude other nested files merely because they have the same basename. Historical phase records are preserved. Parent review, an immutable candidate commit, actual Linux execution and its independent operational audit remain separate next steps; this package does not claim those steps occurred.
