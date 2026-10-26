# Genuine recursive TT dimension bounds: frozen author replay

Author `/root/recover_geometry`. Executed 2026-10-26T19:09:16.489813+00:00 using pinned Lean4.33.1 commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, LeanCert kernel mode.

The two new frozen modules prove arithmetic properties of the actual frozen `stepRank` and `stepInput` format. For all natural dimensions and requested ranks, including zeros, the child entry product and contracted dense count do not exceed the parent entry product. A recursive call shortens the format by exactly one mode. For positive modes and positive ranks at actual cuts, the capped rank, suffix product and compressed child mode are positive. Positive-rank requirements are bounded by actual cut positions, so no positivity of unused zero-extended original ranks is assumed.

`Dimensions.Reachable` records precisely the frozen recursive format `(m::n::ns) → ((stepRank m (n::ns) r*n)::ns)` with the original rank profile shifted by the level. Its invariants are proved by induction: all current modes and actual requested ranks are positive, current product is ≤the original product, current length plus level is the original length, and the remaining tail is the original mode list dropped by level+1. The original shape/rank bridge uses the unchanged original assumptions modes≥2, order≥3 and all actual prescribed ranks≥1.

`Reachable.original_step_bounds` derives at original N=DenseSize the actual input count m*cols≤N and contracted count q*cols≤N, child dense product≤N, rows/cols/q/childmode≤N, all required positivities, and m²/mq/cols²≤N². These justify the N-cell dense work reservations and N² frame/SVD reservations without assuming a rectangular product bound. `original_suffix` identifies the numeric cardinality with the unchanged original suffix list product. Matrix bases and actual RAM execution are separate contracts.

Final fresh author replay PASS: 27 project sources plus literal consumer, 28 kernel commands, all31 explicit authored declarations checked. No project objects reused; pinned external package caches reused. All printed axioms are within `propext`, `Classical.choice`, `Quot.sound`, with no sorry axiom. All live/snapshot sources, previous frozen layout/selector/radix/recursive sources, runtime/statement pins and 25 original review inputs pass unchanged hash checks before and after replay. The consumer expands the arbitrary-natural product reduction, actual original reachable work/square bounds, original tail equality, two-mode termination and zero requested rank.

Source lock SHA-256: `728737eeb3f3c75030b539e2d939f94bea2c0b18d986d8abf4550961e255fbea`.
Result SHA-256: `93f591d28774eb9ec6c4c2fa52b9a01a2d34e46e11e7a0c20939b14f0f99566b`.
Replay driver SHA-256: `d4e407ddf5f8b850e56f7ec9fecf985c8a081d2274dca79a7ba6c9e060766f92`.
Consumer SHA-256: `6382eba7ec329971dc05db48d573bef361cec1f21a492ff197b1ff88a7086f7a`.

Reproduce with `python3 docs/lean/proofs/TR-04/campaign-2026-10-23/tt-dimension-author-2026-10-26/replay.py --output /absolute/new/output/path` in this clone. The output must not contain project objects. The initial interrupted `run/` is a development attempt; the final run is the sole acceptance replay. The driver was strengthened before final execution to check the full selector closure as well as the prior layout and recursive inputs. No frozen proof sources changed between runs.

This receipt covers author verification of the two dimension modules. Independent review, the complete actual TT execution/charged bound and literal Target, Linux CI and Comparator acceptance remain separate gates.
