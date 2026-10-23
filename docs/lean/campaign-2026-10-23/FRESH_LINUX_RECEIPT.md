# Fresh Linux verification of all three complete targets

[PR #366](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/366), [run 39995308565](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39995308565), freshly verified the complete SP-12, TR-14 and PF-05 Targets in the repository's real Linux sandbox with the unchanged Comparator, default kernel and LeanCert kernel consumer. Statement-boundary and permanent-ID workflows also passed.

The head is `cc8f375f3d79ce7d3b7053526638ed37c9125e92`; the actual executed merge is `738e828fef5095e6f782a14bc68783a49a35212b`, with parents published main `5487945e` and that head. The [independent fresh audit](fresh-linux-pr366/REVIEW.md) passes all 126 checks, covering all 325 package inputs, 183 Lean inputs and 171 source/export copy pairs. Every input is identical in the executed merge, head, current worktree and prior reviewed checkpoint `42d16658`. No metadata identity is relabelled to satisfy an older checker; the independent auditor explicitly checks both commits and their parent relation.

| Target | Job | Artifact ID | Original ZIP SHA-256 |
| --- | --- | --- | --- |
| SP-12 | [120557399244](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39995308565/job/120557399244) | 12520885067 | `bd452c46cd5657badc5aaaec474d1d6c913e8b18d704bef416fc30c849af8e69` |
| TR-14 | [120557399236](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39995308565/job/120557399236) | 12519239053 | `d4d99a9ce55b75a7bea237995c522377b2fae305505ec510fdcb4e3b2411e265` |
| PF-05 | [120557399423](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/39995308565/job/120557399423) | 12519698144 | `cb0064e0388bb40708540a807c8f9174898c88fd51f2acf6ed0ec63638d8f306` |

Each actual result is `comparator-accepted` and `kernel-checked`. The selected declarations are the literal original `NLA.SP12.target`, `NLA.TR14.target` and `NLA.PF05.target`, with exactly propext, Classical.choice and Quot.sound. The audit checks all actual theorem-kind/axiom consumers and real sandbox/raw-kernel/Comparator/sorry/native controls, authentic metadata, raw checkout/upload logs, original ZIP hashes and all extracted members. The original evidence, generated consumers, per-target audits and machine-readable 126-check report are retained under `fresh-linux-pr366/`.

This receipt adds fresh merge-context evidence to the earlier independently audited source and promotion receipts. No proof package, original problem, mathematical statement, ID, canonical path or verification safeguard is changed. The integration snapshot remains 83 Lean verified and 35 Solved; the overall goal is active and incomplete. These record complete results for three targets, not completion of the remaining campaign.
