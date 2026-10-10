# MF-23 isolated Linux Comparator and LeanCert receipt

The [GitHub Actions job](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/38006337671/job/114076127209) for commit `7edb593ceb52e28c627adee613f7526f13394d7c` completed **successfully** on 10 October 2026. It validated the formalization manifest, prepared the unprivileged Linux sandbox, ran the fresh Comparator challenge/solution check and all checker controls, and audited the selected `Solution` export with pinned LeanCert in kernel mode.

The completed job log reports `Lean default kernel accepts the solution`, then prints the transitive axiom set for `NLA.MF23.canonical_crouzeix` as exactly `[propext, Classical.choice, Quot.sound]`, followed by `PASS: fresh Comparator run and all controls`. The full log and artifact remain attached to the linked immutable CI job. This is a kernel and boundary receipt for the independently reviewed canonical bridge; its mathematical scope is described in `CANONICAL_BRIDGE_INDEPENDENT_REVIEW.md`.

The receipt is for MF-23 only. The overall 77-project matrix may still be running; other selected targets require their own successful jobs.
