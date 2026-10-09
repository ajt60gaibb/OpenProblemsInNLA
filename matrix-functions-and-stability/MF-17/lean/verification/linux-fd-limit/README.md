# Initial isolated build: open-file limit

On 30 September 2026, the first complete fresh run against commit
`ac582d01532a914538cbfb74863437b18433038a` passed all infrastructure controls
and built Challenge, then failed building Solution with `Too many open files`.
The [actual Comparator log](comparator.log) records exit 1. This run did not
verify MF-17.

The invoking shell's higher limit did not propagate to transient services
started by the systemd user manager. The runner's user-manager configuration
was corrected to `DefaultLimitNOFILE=65536:65536`, and a new transient service
confirmed both limits were 65536. The proof sources and pinned checker were
unchanged. A new `harness.py verify` run starts again with all controls and a
fresh committed project copy.
