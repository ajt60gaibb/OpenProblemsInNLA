# Shared-filesystem build failure

On 30 September 2026, another fresh run of source commit
`ac582d01532a914538cbfb74863437b18433038a` passed the controls, prepared
Mathlib, and built Challenge, then failed during the Solution build with
`Too many open files`. The [actual Comparator log](comparator.log) records
exit 1. This run did not verify MF-17.

The runner's transient service reported soft and hard limits of 65536.
Sampled Lean processes likewise had those limits and only 12–13 descriptors
open. Thus increasing the process limit alone did not resolve the problem.
The failing Mathlib paths were on the host-shared filesystem. This implicated
shared-filesystem I/O under concurrent builds, without establishing its exact
internal cause.

The next fresh run places dependencies and build outputs on the native Linux
filesystem. The unchanged installed toolchain was relocated to free sufficient
space, and remains mounted read-only at its recorded runner path. No proof,
statement, checker, sandbox, or axiom policy was changed.

A [follow-up build](toolchain-shared-comparator.log), with native Mathlib files
but the toolchain on the shared volume, also failed with the same error,
now naming `/tmp/mf17-lean/lib/lean/Std/Do/SPred/SPred.ir`. The subsequent
setup therefore keeps both the toolchain and all freshly extracted dependencies
and build outputs on native Linux storage. Only the committed source checkout
and compressed download cache reside on the larger volume.
