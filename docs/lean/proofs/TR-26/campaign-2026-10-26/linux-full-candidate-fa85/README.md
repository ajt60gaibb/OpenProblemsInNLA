# TR-26 full-target Linux CI receipt collection

This directory holds proof-author collection and mechanical audit of genuine
GitHub Actions evidence for the full TR-26 candidate on PR 369. It is separate
from the retained isotropic-only receipt. It does not replace independent source
or package review, and it does not promote canonical metadata.

The corrected candidate is `fa85c05acc70bbaa05bb3346fb43b57b1546af67`.
Its PR Lean run is `40396604016`, with project job `121831441827`.
The successful run and 2,391-check author audit are summarized in
`AUTHOR_CI_RECEIPT.md`; the complete report is
`corrected-candidate-audit/AUTHOR_CI_RECEIPT.json`. The exact inputs are
856 package-locked files plus `PACKAGE_LOCK.json`,
84 runtime Lean sources, and 80 exact shared copies from reviewed full source
`ecc597cb68b65b473aecce9ac635e27d35c09694`.

The exact Comparator exports are:

- `NLA.Proofs.TR26.nonisotropic_degree`
- `NLA.Proofs.TR26.isotropic_degree`
- `NLA.Proofs.TR26.target`

There are no replaceable definitions; permitted axioms are only `propext`,
`Classical.choice`, and `Quot.sound`.

```sh
python3 collect_ci.py --run 40396604016 \
  --head fa85c05acc70bbaa05bb3346fb43b57b1546af67 --output retained
```

After the job completes and the actual checkout Git object is available:

```sh
python3 audit_ci.py \
  --repo /Users/ajt253/.codex/worktrees/tr26-exact-degree-oct26/OpenProblemsInNLA \
  --head fa85c05acc70bbaa05bb3346fb43b57b1546af67 --run 40396604016 \
  --evidence retained/run-40396604016/terminal --output corrected-candidate-audit
```

The offline audit never invokes Lean, Comparator, the verification harness,
a sandbox, or network requests. It reads immutable Git objects and the retained
raw API metadata, separately downloaded raw job log, and original artifact ZIP.
It derives the executed synthetic merge from the actual checkout log and checks
its Git parents, rather than inferring it from mutable nested PR metadata.

The first full candidate `f0fc0691c3496822e330894de60a9d6e94b7890a` and run
`40395797108` are superseded for package completeness. Both independent package
reviewers found a locked ignored Python bytecode file absent from Git. The exact
old auditor, lock, Git path inventory and mismatch diagnostic are preserved in
`diagnostics/f0fc-ignored-bytecode-input/`. No receipt for that candidate is
accepted as a complete package receipt. The corrected audit checks all 332
existing review-evidence bindings, the explicit generated-bytecode omission,
and all 92 unchanged executable/pin inputs.

A successful `AUTHOR_CI_RECEIPT.json` remains an author-collected receipt pending
root's separate independent audit. A later metadata promotion may create another
run; its source and receipt must be bound separately.
