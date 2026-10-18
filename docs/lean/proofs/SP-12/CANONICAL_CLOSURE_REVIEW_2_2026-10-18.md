# SP-12 completed canonical package — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
**APPROVE the exact completed canonical proof package for its unchanged full Target.** I authored no SP-12 proof, statement or canonical wrapper. This local independent review does not itself claim Linux Comparator acceptance.

Canonical package: `eigenvalues-and-inverse-problems/SP-12/lean`. `Solution.lean` has SHA-256 `d09d569d4e099c60ed12fb9a896f551dceb86f1f3685dff391395c5be6bd0369`. It exports the literal `NLA.SP12.target : NLA.Statements.SP12.Target` and directly applies the exact copied complete shared proof `NLA.Proofs.SP12.target`. No additional parameters, hypotheses, definitions or axiom permissions are supplied by the wrapper.

The full proof's mathematical source review is [CLOSURE_REVIEW_2_2026-10-18.md](CLOSURE_REVIEW_2_2026-10-18.md), with the preceding eight support modules in the preserved support review. Every one of the 51 local closure sources is byte-identical to the reviewed shared source and its two source-lock digests. These are 48 proof modules (36 SP-11 prerequisites and 12 new SP-12 modules), plus three statements/infrastructure files. The exact canonical Lean source set is those 51 copies plus Reviewed.SP12, Challenge, Identity and Solution: **55 files**.

The independent [copy/boundary audit](verification/canonical-copy-review.json) passes all ten checks, including all 51 exact copies, all locked exports, the exact 55-file set and the unchanged frozen comparison boundary. Original and numerical source archives, statements, Challenge, Identity, Comparator config and all pins match the pre-Solution lock. The only semantic lakefile changes are adding the copied SP-11 prerequisite library glob and the Solution library/default target. The original canonical README is still byte-identical to retained ORIGINAL at this checkpoint. Both independent pre-Solution boundary approvals remain retained. This does not rewrite either historical boundary approval to claim it covered a later proof.

The actual Comparator boundary remains exactly one theorem, `NLA.SP12.target`; definition replacements are empty and permitted axioms are exactly `propext`, `Classical.choice`, `Quot.sound`. Identity proves live/frozen Target equality by `rfl`, so both export and independent reviewed proposition are definitionally the original complete PSD/SAP/chromatic statement.

An immutable fresh-source audit passed **56 Lean commands**: all 55 actual source files plus a generated consumer. The consumer imports Solution and Identity, checks **379 explicit declarations**, including **270 theorem/lemma constants**, enforces `.thmInfo` proof kind, and checks LeanCert kernel trust and transitive printed axioms. It additionally requires the selected target's literal unchanged proposition type, without parameters. It checks the actual mangled private helper theorem by unique environment lookup, theorem kind and the same kernel command. All ten tracked dependency pins and all frozen project source bytes passed before/after. All project output objects are rebuilt in a fresh private prefix; pinned cached dependency objects alone are reused.

Challenge is compiled as a separate build-only module. It is deliberately not imported into the proof consumer alongside Solution, since the two comparison modules intentionally define the same selected theorem name. Challenge's placeholder is never treated as a trusted proof; the retained pre-Solution negative kernel check rejects its exact unchanged bytes for `sorryAx`.

Reproduce from the repository root:

```bash
python3 docs/lean/proofs/SP-12/verification/check-package-copies.py
python3 docs/lean/proofs/SP-12/verification/check-support.py \
  --project eigenvalues-and-inverse-problems/SP-12/lean \
  --root-module Solution Identity --build-only-module Challenge \
  --target-theorem NLA.SP12.target --evidence-name canonical-full-target-review
```

Exact snapshots, corrected consumer, driver/compiler identities, raw logs and the complete result are in [verification/canonical-full-target-review/](verification/canonical-full-target-review/). The initially overly strict lakefile string comparison (before the SP-11 prerequisite glob was accounted for) is preserved as `canonical-copy-review-attempt-1.json` with its driver; the corrected structural check allows exactly the two intended library additions and no other configuration change.

This is local macOS Lean 4.33.1/LeanCert kernel evidence with the three standard axioms, not an SP-12 Linux receipt or external human peer review. I authored five historical SP-11 supports; their independent source reviews are by other agents. This report gives unchanged prerequisites fresh runtime/copy evidence, not independent self-review. No proof/project source, statement, permanent ID or original page was changed for this audit.
