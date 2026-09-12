# RA-07 reviewed Linux candidate handoff

**Ready for root packaging review and an immutable Linux candidate commit. Actual Linux verification remains pending.** Canonical status remains `Solved`.

Worktree: `/tmp/nla-lean-ra07-worktree`  
Branch: `codex/lean-ra07-symmetric-ratio-convexity`  
Base: `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`

The current project README now reports the complete six-export proof, both statement approvals, both independent final proof approvals, exact original scope, kernel-only LeanCert auditing of algebra/root geometry, reproducible explicit build targets, and the pending Linux gate. The new `formalization.yaml` conforms to the actual pinned v0.4 schema and advertises exactly the six Comparator-selected declarations. It claims no interval calculation or numerical certificate.

Mathematical source credit stays Matthew J. Colbrook. Formalization credit is George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA; no George email is added.

| Current publication metadata | SHA-256 |
| --- | --- |
| `README.md` | `a67e227315739c359a6a439741a0df0ef0300945d42b89ef003f74b50fb8b398` |
| `formalization.yaml` | `b579c4eeedec491de21e11ff5a87461e1398d53179e33e3e8a23dc9dbc7586db` |
| `verification/linux-candidate-2026-09-12/packaging-record.json` | `b3673987f508947d1bc62b0ee2492f1854825ab5e844f2f1d57b625ad3272725` |

Both independent final approvals remain unchanged:

- Referee 1: `reviews/proof-referee-1.md`, SHA-256 `3b232fe78975ae885909a7e805686e32db0b4db9e65760502a55795460d398e3`.
- Referee 2: `reviews/proof-referee-2.md`, SHA-256 `23f5e33d7992bcf204a183b6a71f634e029ed0cc0b06a8e85bedfe35c06046c8`.

The original proof-freeze SHA-256 remains `ecd94daf2dee9fe4625e09f1a08026eb75ac8a14bea6efb688921a3e78eb6b4a`. Its only superseded current file is the statement-stage README; that exact old README is archived in this directory with SHA-256 `797cecf5a659d33db983f5ffabfb445fd750ee6a381d3c5efc9eb5b282cef237`. All 37 remaining freeze inputs, all prior review/evidence files, all three original mathematical sources, and every mathematical/configuration byte match the reviewed versions. None of the original freeze or review records was rewritten. Of 110 previously publishable project inputs, only the current README changed.

Completed packaging checks:

- Actual v0.4 schema and Comparator coverage: PASS for six declarations.
- Permanent problem IDs against `origin/main`: PASS for 217 IDs.
- Permanent-ID test suite: all 17 tests PASS.
- README relative links, exact protected hashes, all prior evidence, unchanged canonical sources, ten clean dependency pins, and artifact exclusions: PASS.
- Git tracked and staged diffs: empty. The entire project remains an untracked addition on its isolated branch.

Raw successful validator/test outputs, the packaging checker and results, original-input hashes and current evidence manifest are retained here. `EVIDENCE-MANIFEST.json` hashes this handoff and every other file in the packaging evidence directory except itself. The packaging checker did not re-run mathematical proof compilation; the mathematical bytes already passed both independent final reviews and are unchanged.

No catalog regeneration, canonical edit, PDF render, commit, push, PR or Linux run was performed during packaging. The coordinator retains the commit/push and actual Linux verification steps. The final immutable verification revision and successful original artifacts must be audited before any `Lean verified` promotion.
