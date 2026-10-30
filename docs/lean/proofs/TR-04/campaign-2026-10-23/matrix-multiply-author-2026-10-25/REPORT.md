# TR-04 strided matrix multiplication author replay

Author `/root/recover_geometry`, 2026-10-25. The three new `MachineMatrixMultiply*` sources are frozen by `source-lock.json`, SHA-256 `a6c4e691c3d218a7318bddc0c4922833e542951dd01af51500c15aecbbc2a017`. The fixed actual program has 22 labels, 17 natural registers, three real registers, and no constant pool. Its only instructions are ordinary tests, register arithmetic, reads, writes, and halt.

`MatrixMultiplyData.leftMatrix` and `rightMatrix` read literal strided addresses from the old memory; the strides can be zero and the input arrays can overlap each other. `InputsOutsideOutput` requires only the actual in-range input entries to lie outside the dense output block. The source proves ordinary dense and transposed `readMatrix` identities and derives this condition from dense `DisjointBlocks`.

The all-trace endpoint `matrixMultiplyProgram_run` starts with explicit parameter registers and old memory. Every legal trace halts at D after `((8*k+11)*n+4)*m+2` transitions, returns exactly the actual product of the two strided matrices, preserves every address outside D, and has actual `CostThrough` bounded by `17*(m+k+n+1)^3`. Legal trace existence is proved unconditionally. All natural dimensions, including zero, are covered. The implementation sums actual read memory entries; the final product statement is proved from that loop invariant rather than assumed in a program gate.

Fresh author replay passed all 14 project source compilations plus a separate literal scalar-program consumer. All 56 explicit new public declarations have kernel assertions; all printed axiom lists use at most `propext`, `Classical.choice`, and `Quot.sound`. Lean 4.33.1 compiler `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` checked the replay. No project objects were reused; pinned external Mathlib/LeanCert objects were reused. All earlier frozen radix/recursive sources and all 25 original review inputs remain unchanged.

Receipt `run/result.json` SHA-256 `175d8a47f4c114ec31d712cfd515ac0ee8090fe20219b53f286a430c1f3fe060` binds the generated consumer and logs. This is author evidence for a multiplication component; it is not independent approval, a complete TT program/Target, Linux CI, or Comparator acceptance.

Reproduce with `python3 docs/lean/proofs/TR-04/campaign-2026-10-23/matrix-multiply-author-2026-10-25/replay.py --output /absolute/new/output`.
