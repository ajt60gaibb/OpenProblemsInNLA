# TR-04 callable multiplication author replay

Author `/root/recover_geometry`. Campaign date 2026-10-25; replay completed at `2026-10-26T01:47:06.601267+00:00`. New source `MachineMatrixMultiplyCallable.lean` SHA-256 `f1de586a5804f1deddf9f82650dd71aa4521d3f8b6def958ff7df0b07b9f0382` is frozen by lock SHA-256 `ffe94faed554359e9fe68f8e487dac3e4188d75cd7b1ee62be3535ca307d5d36`. All three prior multiplication sources and the four root relocation sources remain unchanged. The dependency lock binds the exact frozen `MachineNoEarlyHalt` and root relocation evidence lock.

The local return occurs after `matrixMultiplyRowTime p * p.rows + 1` transitions at label 21 with status running, before executing the local halt. It retains the actual matrix product and outside-output old memory. A proved running endpoint supplies the no-earlier-halt condition through the generic actual-state helper; there is no new termination assumption.

`RoutineEmbedding.matrixMultiply_run_at` works at every caller trace offset under the literal finite code/register embedding. It returns the related running state at the caller's mapped continuation, with actual charged-prefix cost at most the prior caller cost plus the return time, hence plus `17*(m+k+n+1)^3`. Every caller real and natural register outside the injected frame is preserved. The companion `matrixMultiply_product_at` exposes the caller label, running status, actual product readback, outside-output memory, cubic cost and outside-frame registers directly. All dimensions and strides retain the previous generality.

Fresh replay passed 21 project source compilations and an independent generated exact-type arbitrary-caller consumer (22 commands). All nine new explicit declarations have kernel assertions and axiom reports containing at most the standard three axioms. No project objects were reused; pinned external Mathlib/LeanCert caches were reused. Lean 4.33.1 compiler `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` checked this result. The prior radix/recursive sources, frozen matrix sources and all 25 original review inputs remain exact.

Receipt `run/result.json` SHA-256 `d1d6c18d8be29842b893268313aa44bdc67e50b478c4c6573f94f038b67179f8`. This author evidence covers a callable multiplication component, not an independent review, complete TT program/Target, Linux CI or Comparator acceptance.

Reproduce with `python3 docs/lean/proofs/TR-04/campaign-2026-10-23/matrix-multiply-callable-author-2026-10-25/replay.py --output /absolute/new/output`.
