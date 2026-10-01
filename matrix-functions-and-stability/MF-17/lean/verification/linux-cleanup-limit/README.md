# Accepted proof check; incomplete harness cleanup

On 30 September 2026, the fresh run against
`ac582d01532a914538cbfb74863437b18433038a` built Challenge and Solution,
compared all five contracts and their permitted axioms, and replayed the
proof successfully through Lean's default kernel. The actual
[Comparator log](comparator.log) and [receipt](result.json) record acceptance.

**The overall harness nevertheless exited with status 2.** Its fresh-copy
cleanup encountered the generated-output mount before that mount was detached:
`Device or resource busy`. The [driver log](driver.log) records this error.
This directory must not be presented as a clean successful harness run.

The subsequent fresh run detaches that output-only mount as soon as the
Solution build's success message appears, before proof export and normal
cleanup. The source, checker, comparison, axiom policy and kernel replay are
unchanged. Only a subsequent complete exit-0 run supports promotion.
