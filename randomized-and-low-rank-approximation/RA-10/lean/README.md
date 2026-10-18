# RA-10 isolated proof verification

This project selects the complete frozen `NLA.ReviewedStatements.RA10.Target` for
Comparator. `Identity.lean` proves that it is definitionally identical to the
live `NLA.Statements.RA10.Target`. `Solution.lean` uses the full theorem
`NLA.Proofs.RA10.ra10_target`, whose witness is the universal constant 11.
The canonical page retains its complete original question and permanent ID.

Lake pins the substantive proof package at commit
`844237f7e979146c937c0dc88f5c3f6e5f40c9b9`, using its
`lean-statements` subdirectory without copying the large proof library.
`source-lock.json` binds the original reviewed canonical README snapshot,
live and reviewed statements, final proof theorem, and the existing complete
source-hash manifest. The
current canonical README adds only status and evidence before the original
question; the statement-preservation gate compares the complete suffix from
the question through the end of that page byte-for-byte with `ORIGINAL.md`.
The project uses Lean 4.33.1, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926` in kernel mode.

On credential-free non-root Linux with the repository's supported isolation:

```bash
python3 tools/lean/validate_manifest.py randomized-and-low-rank-approximation/RA-10/lean
tools/lean/bootstrap.sh /tmp/nla-ra10-tools
tools/lean/verify.sh randomized-and-low-rank-approximation/RA-10/lean /tmp/nla-ra10-tools
```

The shared `lean-verification.yml` workflow selects this canonical project.
The [isolated Linux receipt](../../../docs/lean/proofs/RA-10/LINUX_CI_RECEIPT.md)
records an accepted Comparator proof and LeanCert kernel trust with only the
three standard axioms. Two independent AI-agent source reviews are retained in
`reviews/`. The local 3,044-job source build is historical supporting evidence.
