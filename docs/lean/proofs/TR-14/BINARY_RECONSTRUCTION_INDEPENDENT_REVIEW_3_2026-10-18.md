# TR-14 actual recurrence, Vandermonde reconstruction and binary upper width — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
I authored none of these modules. **APPROVE these exact three support sources.** Their upper-width theorem retains explicit normalized least-apolar-chart hypotheses. It is not the all-width TR-14 Target or an ordinary lower bound.

| Module | SHA-256 |
| --- | --- |
| `MomentRecurrenceReconstruction` | `61b4154987b1935f2f24de4df404d0d3c2a6a07c7a06536294617d1e72ea6c91` |
| `VandermondeReconstruction` | `caa1276f4cfa69301c2318e66efc768c4fba410dffd927cb8250c82838d171f7` |
| `TR14BinaryUpper` | `4be7224a843ebd1efcfb61a51a44b05ac8d82f8a16828b2302bced5943729cda` |

`MomentRecurrenceReconstruction` proves literal finite-vector uniqueness for the existing recurrence. Strong induction handles each available moment: indices below the polynomial degree use initial equality; every other index is the guarded shifted leading term, whose remaining indices are strictly smaller and still within the supplied moment vector. The degree-zero recurrence forces every available moment to zero, and an empty shifted range is not silently extrapolated. Weighted powers of actual roots satisfy the same recurrence by evaluating the monic polynomial, multiplying by the shift and interchanging finite sums. No recurrence uniqueness or infinite extension oracle is assumed.

`VandermondeReconstruction` enumerates the actual roots of the monic separable complex polynomial through its root multiset/finite-set cardinality, obtaining exactly degree-many distinct nodes. The polynomial is nonzero by monicity. The actual square Vandermonde matrix has nonzero determinant from node injectivity, so its row-multiplication map is surjective and gives coefficients matching the first degree-many supplied moments. Orientation is correct: its row-weighted column j is exactly the sum of coefficient times node-to-the-j. The degree bound ensures every initial coordinate exists. Recurrence uniqueness and the proved root-power recurrence extend this equality through every available moment.

The final width conversion is the exact frozen symmetric definition: one common vector per term has coordinate `z_i^j`, independent of tensor mode. The product of these coordinates is the node raised to the sum of the zero-based tensor indices, which is precisely the frozen Hankel index. Zero roots remain allowed (`0^0` has its ordinary polynomial value), as do degree zero and degree D+1. Degree zero gives an actual empty sum for the necessarily zero moment vector; degree D+1 uses initial matching for all moments and no recurrence step. No positivity, nonzero-node, generic-tensor, distinct-input-moment or preprovided reconstruction-coefficient assumption is added. The generic reconstruction source itself imposes no tensor order/dimension restrictions beyond its explicit degree and recurrence conditions.

`TR14BinaryUpper` directly combines the previously independently reviewed actual separable-apolar polynomial construction with this actual reconstruction. Positive least-apolar degree gives `D-r+2 ≤ D+1`, so the requested width is exactly `D-r+2`. Nonzero input, monic minimal apolar polynomial, its positive degree bounded by D, and the explicit half-degree bound remain visible. These conditions have not been replaced with an unproved all-tensor chart theorem here. General chart transport/selection and the ordinary-rank lower comparison remain separate obligations for the full Target.

The independent immutable-source run passed **17 Lean commands**: 16 actual local sources plus a separate consumer. It includes these three sources, the previously reviewed three-module binary construction, eight imported proof foundations and two statement/infrastructure files. The consumer checks **46 explicit declarations**, including **40 theorem/lemma constants**, their actual theorem kind, LeanCert kernel trust and transitive printed axiom closure. Private foundation theorem constants are resolved uniquely by actual environment names and checked with the same proof-kind/kernel commands. Only `propext`, `Classical.choice`, `Quot.sound` occur. All ten pinned dependency trees and all source bytes passed before/after. All local objects are freshly rebuilt into a private output directory; campaign project objects are excluded and pinned dependency objects alone are reused.

Reproduce from the repository root:

```bash
python3 docs/lean/proofs/TR-14/verification/check-binary-reconstruction.py \
  --top TR14BinaryUpper --evidence-name binary-reconstruction-review-3
```

Exact source/consumer snapshots, driver/compiler hashes, dependency checks, raw output and result are in [verification/binary-reconstruction-review-3/](verification/binary-reconstruction-review-3/). The prior [three-module binary construction review](BINARY_CONSTRUCTION_INDEPENDENT_REVIEW_3_2026-10-18.md) remains separate, and imported foundations retain their existing source reviews. This is independent mathematical/source review of the three newly frozen modules plus fresh kernel evidence for their exact local closure, not a new semantic review of every retained TR-14 proof. It is local macOS Lean4.33.1 evidence, not a Linux Comparator receipt, full Target proof, external human peer review or source-author endorsement. No proof, statement, original canonical page or permanent ID was edited for this audit.
