# TR-26 isotropic Linux CI receipt collection

This directory holds proof-author collection and mechanical audit of genuine
GitHub Actions evidence for PR 369. It does not provide independent source
review, run a local build as Linux evidence, or claim the full TR-26 Target.
The selected Comparator theorem is only `NLA.Proofs.TR26.isotropic_degree`.

Initial proof-package head: `6c607ab14af2b8b2b8075f0b3f1798e037c10899`.
Initial PR Lean run: `40390314938`. The later head
`04045bad74f9dff03488b3b9080b081f397e5349` changes only the generated statement
inventory, outside the canonical package. The audit checks every package byte
against both heads and the checkout actually executed by CI.

The raw collector is read-only against GitHub. Every call retains a timestamped
API snapshot; terminal collection preserves the separately fetched raw job log
and original artifact ZIP, with its API digest and byte count.

```sh
python3 collect_ci.py --run 40390314938 \
  --head 6c607ab14af2b8b2b8075f0b3f1798e037c10899 --output retained
```

Once the job has completed and its checkout Git object is available locally,
the offline author audit reads immutable Git objects and the retained receipt:

```sh
python3 audit_ci.py \
  --repo /Users/ajt253/.codex/worktrees/tr26-exact-degree-oct26/OpenProblemsInNLA \
  --evidence retained/run-40390314938/terminal --output initial-run-audit
```

The audit never invokes Lean, Comparator, the verification harness, a sandbox,
or network requests. It reconstructs only the harness's pure consumer source
generator to check its hash. A successful `AUTHOR_CI_RECEIPT.json` remains an
author receipt pending separate independent audit.

`AUTHOR_SUPPORT_FREEZE.json` retains exact hashes and accepted local kernel
receipts for this author's 30 frozen TR-26 support modules. Several are later
nonisotropic support modules outside the isotropic package; the CI audit does
not extend its selected theorem or input set to those modules.
