# TR-04 explicit radix and machine layout author replay

Author: `/root/recover_geometry`. Date: 2026-10-25.

The three new sources are frozen by `source-lock.json` (SHA-256 `c8c40258fc55ef6ccc8cab619aff0ba667c9721ceda403c6dae5ba4e16b68d06`). The replay passed 32 fresh project source compilations and one separately generated consumer with pinned Lean 4.33.1 (`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`). No project objects were reused; the pinned external Mathlib/LeanCert package cache was reused. All 37 new public declarations have kernel trust assertions and printed axiom lists containing only `propext`, `Classical.choice`, and `Quot.sound`.

`TensorCompressionRadix` constructs an explicit last-index-fastest finite radix equivalence, proves its numeric inverse, and identifies its original-model offset with the literal `Offset`. `TensorCompressionRadixSVD` proves actual matrix rank/energy reindex identities and transports every literal `ValidSVD` right-column response to the frozen completion relation while preserving U and sigma. `TensorCompressionRadixDecode` proves both literal `Decode`/`Offset` inverse directions, valid-address coverage, and the actual dense `InputMemory` tensor cell equation. Formats include empty lists, zero dimensions, and compressed dimension one; original-model statements retain their original Shape assumptions.

The consumer checks the literal original `Decode`, `Offset`, `InputMemory`, `ValidSVD`, actual rank constraints, squared Frobenius error, and sInf optimum. All frozen eleven recursive sources and all 25 original review inputs remain unchanged. This is author evidence, not an independent approval, strict Target, executable program/runtime, Linux CI, or Comparator result.

Reproduce in a new output directory:

```sh
python3 docs/lean/proofs/TR-04/campaign-2026-10-23/radix-interface-author-2026-10-25/replay.py --output /absolute/new/output
```

Receipt `run/result.json` SHA-256: `13f249591aa437e3c21271a33abd2483c6da03df82a4a4e4c4127975a2bf9414`. Source and consumer logs and the generated exact-type consumer are hash-bound in that receipt.
