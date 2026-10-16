# RA-10 isolated proof verification candidate

This project selects the complete frozen `NLA.ReviewedStatements.RA10.Target` for
Comparator. `Identity.lean` proves that it is definitionally identical to the
live `NLA.Statements.RA10.Target`. `Solution.lean` uses the full theorem
`NLA.Proofs.RA10.ra10_target`, whose witness is the universal constant 11.
Neither the canonical problem nor its Solved status changes in this draft.

Lake pins the substantive proof package at commit
`844237f7e979146c937c0dc88f5c3f6e5f40c9b9`, using its
`lean-statements` subdirectory without copying the large proof library.
`source-lock.json` binds the canonical README, live and reviewed statements,
final proof theorem, and the existing complete source-hash manifest. The
project uses Lean 4.33.1, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926` in kernel mode.

On credential-free non-root Linux with the repository's supported isolation:

```bash
python3 tools/lean/validate_manifest.py randomized-and-low-rank-approximation/RA-10/lean
tools/lean/bootstrap.sh /tmp/nla-ra10-tools
tools/lean/verify.sh randomized-and-low-rank-approximation/RA-10/lean /tmp/nla-ra10-tools
```

The shared `lean-verification.yml` workflow selects this canonical project on
this PR. The RA-10 source theorem previously passed a local 3,044-job Lean
build and printed only the three standard axioms. A fresh isolated Linux
Comparator receipt and independent final review of the full proof are still
required before changing the catalog status to Lean verified.
