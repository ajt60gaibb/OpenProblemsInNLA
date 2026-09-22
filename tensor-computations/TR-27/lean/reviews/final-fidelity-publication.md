# TR-27 final fidelity review: publication documentation

Reviewer: `/root/tr27_final_fidelity`, independent nonauthor Codex AI referee. **Verdict: APPROVE the final publication content and reviewed documentation delta.** This supplements the unchanged [source review](final-fidelity-referee.md) and [verification completion review](final-fidelity-completion.md); it does not rewrite their historical receipts or imply that later prose was an input of the earlier Linux run.

I read the final canonical verification notice, current Lean project guide and metadata, the new RESOLVED entry, the catalog changes, and the TR-27-only renderer delta. The claims accurately state the complete original negative answer and the inspected verification evidence, preserve George Stepaniants's requested affiliation and Colbrook's mathematical credit, disclose AI roles, and distinguish optional manuscript strengthenings. The metadata correctly says that the variety contains a point of rank 3 and border rank at most 2 whose ordinary Segre tensor square has rank 9. It does not assign those ranks to the variety itself.

The canonical page now records Lean verified status with the verification date, while its complete original Problem statement, Why it matters, References/status history, earlier resolution attribution and author feedback retain their original bytes. The title, permanent TR-27 path and append-only ID registry are unchanged. Removing just the new TR-27 paragraph from RESOLVED recovers its prior complete contents. The catalogs change only the evidence classification and corresponding counts: 42 solved, 64 Lean verified, still 106 retained resolved entries and 111 open-target entries.

The new [publication delta auditor](final-fidelity-completion-evidence/audit_publication_delta.py) allows exactly two changed files from the 116 original verification inputs: README.md and formalization.yaml, at the explicit final hashes below. It strictly checks all remaining **114** original inputs, including every mathematical module, Definition, Challenge, Solution, numerical target, Comparator selection, toolchain, dependency and build configuration. It also checks the retained 116-input snapshot, old referee reports/receipts and original strict auditor unchanged. Its [record](final-fidelity-completion-evidence/publication-delta.json) and [output](final-fidelity-completion-evidence/publication-delta.log) pass. The older strict auditor is intentionally historical and would reject the later documentation; it has not been weakened or silently rewritten.

The published notice has the previously approved prose. Its reproduction code drops only the syntax-highlighting language tag and wraps one command with shell continuations; the auditor normalizes those documented presentation changes and recovers the exact previously approved notice hash. The commands and their arguments are unchanged.

One renderer finding was resolved: an exact newline match did not recognize the dated verification heading. The final TR-27-specific prefix match now inserts the intended separation, while the original-target page break remains. The other renderer changes are limited to TR-27's verification-date label, header height and reference pagination. They do not change mathematical text or other problem IDs. I approve that code-level content scope; I did not perform PDF visual inspection. Generated PDF/TeX QA and the repository's actual catalog/ID checks remain separately recorded by the coordinator.

The final mathematical and mechanical verdicts remain unchanged. This review is independent AI review, not external human peer review or official Tau Ceti endorsement. Exact hashes are also retained in the [publication receipt](final-fidelity-publication-receipt.json).

| Reviewed file | SHA256 |
| --- | --- |
| `tensor-computations/TR-27/README.md` | `5591cb850a1517fc5997da0b8cb38c13b372417e8703f179ae5ca951c6903069` |
| `tensor-computations/TR-27/lean/README.md` | `a60de9d0e8fa80a99ca5d46f3ebec7f3d7ba0ed6e31bf1a53789d5f567fc2374` |
| `tensor-computations/TR-27/lean/formalization.yaml` | `aff70ae2e8bfbf833ab832e5c7541876a788251bf28b180e9cce36b7efb1fbe9` |
| `RESOLVED.md` | `bc27864dbfe20932a999b24c8769260e7c3cd461a5771cd985418037fbd45690` |
| `README.md` | `206bd61ade1b466f2e0e6e57cf84efdac7f9b8540cae1c152d0d4438ec50752b` |
| `CATALOG.md` | `a4fc908625695820ebe502d2152619863fccd9af9b294e910aaa7a83dd6c4d9e` |
| `tensor-computations/README.md` | `4828d8a8357b5d5076397e5a5acb97f8e3fe08fd7b24cc0d5e48f847a9cc3e6c` |
| `tools/render_problems.py` | `258e4faafbabc44aaa7ac8078c87240742ed70a41884dbc8d1109a26b940fe7b` |
| `problem_ids.json` | `d7f9925a483d40030ef266917bc8e413dac6d45530ad5515da506ffe9583e763` |
