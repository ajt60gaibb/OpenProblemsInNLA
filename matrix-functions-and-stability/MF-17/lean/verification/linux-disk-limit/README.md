# Dependency-cache preparation: insufficient disk space

On 30 September 2026, a fresh retry against source commit
`ac582d01532a914538cbfb74863437b18433038a` passed the controls but exhausted
the smaller Linux filesystem while unpacking the pinned Mathlib cache.
The [actual cache log](mathlib-cache.log) records exit 1. This attempt did
not reach the MF-17 Comparator check and does not verify the target.

The subsequent run uses the larger local volume and the corrected systemd
file-descriptor limit, with the same committed source and pinned checker.
