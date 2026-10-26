# Author audit-driver diagnostics

The initial author audit incorrectly treated the nested
`run.pull_requests[0].head.sha` as immutable. GitHub had updated that nested
field to the later inventory-correction head. The run's own `head_sha` and
`head_commit.id`, the project job's `head_sha`, the raw checkout log, and the
executed Git object's parents consistently bind the original proof head.
The driver now records the mutable nested and live PR fields separately.

Root's independent driver read also found an incorrect copied assumption
about a canonical `TR-26/ORIGINAL.md` path. The canonical README was never
edited. The preserved originals are the package's `sources/ORIGINAL.md` and
`docs/lean/statements/TR-26/ORIGINAL.md`. The exact failed driver and its
1,161-check diagnostic report are retained under
`02-nonexistent-original-path/`, with matching driver SHA256.

The corrected driver compares the complete canonical README and both real
preserved original files against the published README. Neither diagnostic
is a Lean, LeanCert, Comparator, or Linux verification failure.
