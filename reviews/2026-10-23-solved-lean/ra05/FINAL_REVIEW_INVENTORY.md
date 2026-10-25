# Independent final RA-05 hyperplane bridge review

Reviewer: OpenAI Codex AI agent `/root/inventory`, 23 October 2026. Proof author:
`/root/proof_route`. I previously approved the exact support contract and final
outer-product definitions. I did not author the implementation, primary audit,
or the author's replay. I independently read the complete implemented source
and reran it through a separate source-snapshot runner.

**PASS for the three exact support theorems.** No changed premise, residual
definition, weight model or alternate target was found. The eight minimum
support lemmas reviewed separately and these three bridge theorems together
still do not prove RA-05 Classification, universal NegativeAnswer or Target.

| Reviewed input | SHA-256 |
| --- | --- |
| `NLA/Proofs/RA05/HyperplaneDefinitions.lean` | `03c589f029a146203487f4d5ed5982eb67e4a91d64c0ab8f817baf1de898a276` |
| `NLA/Proofs/RA05/HyperplaneBridge.lean` | `2e8d441f6aa46d7344c37762010be9e1afb30574e085bad980bb9bf01e7ccae1` |
| `Challenge.lean` | `0049b6258325a138e0579fd26fcacc772758996f77c3cc9211a3e58a3663ff12` |
| `SUPPORT_CONTRACT.md` | `c2d08bf28f286bf6fa5c9c5e66b8bdf7aceeaa5435377e626051483e4f661552` |
| `SupportAudit.lean` | `9b23e17443c9e4d5966703cce23281291db8c80dda007f2c98a8a5d5752ac9b0` |
| `verification/inventory-review/run_review.py` | `55b5533b890fa53c41c4e66a328ec7d29d2afa412525790b71962f922bb9601d` |
| `verification/inventory-review/result.json` | `00ab4db3675aa5c96f3a6e151a7c015798e18d5ef2987a7775c54f737db5bd88` |

The independent replay compared every SOURCE_LOCK destination, all ten files,
with its immutable published source at
`5487945e5a72abd952b0c89915915de8cc9b3e65`. Every byte and hash matched. It
required the three public implemented theorem headers to equal the three exact
approved Challenge headers. It snapshotted and compiled all six source files
in a fresh temporary output tree and checked that inputs did not change during
replay. All six commands passed with official Lean 4.33.1, compiler commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, on local arm64 macOS. The three
LeanCert `#assert_trust kernel` checks passed; the complete axiom reports for
each public theorem contain exactly `propext`, `Classical.choice`, `Quot.sound`.
The source snapshots, commands and raw logs are retained alongside result.json.

The actual proof discharges every mathematical gate in the approved statements:

- `unitHyperplane_projector` proves symmetry entrywise and idempotence from the
  literal outer-product multiplication and unit dot product. It constructs an
  actual nonzero kernel vector, uses finite-dimensional rank-nullity, and
  derives the natural rank bound. It does not assume determinant singularity,
  the desired rank bound, a generic-position condition or a positive input
  rank. The dimension-one zero projector is included.
- `rowCost_unitHyperplane` proves each actual row residual coordinate equals
  the actual RA06 row action times the same coordinate of the normal. The
  sum-of-squares identity, unit norm and `Real.sqrt_sq_eq_abs` give the exact
  absolute value before the unchanged arbitrary real exponent. There is no
  matrix/row transpose mismatch or approximate norm identity.
- `strongCoreset_implies_allVectorEmbedding` handles the zero vector using
  `p > 0`. For every nonzero vector it proves the squared norm positive,
  constructs an actual normalized unit vector, applies the original coreset
  to the genuine hyperplane projector, and proves exact energy homogeneity.
  Multiplication by the common nonnegative real-power factor transfers both
  inequalities back to the original vector. This is valid for arbitrary real
  accuracy, including when `1 - ε` is negative. The same arbitrary weights,
  matrix, exponent and accuracy appear on both sides throughout.

The final implementation uses multiplication from the unit-vector bounds
rather than the contract's equivalent positive-factor cancellation narrative;
this introduces no extra assumption and proves the same exact signatures.
The positive exponent is used only where the zero test vector requires the
zero-power convention. Arbitrary row counts, empty rows, rank-deficient data,
all positive ambient dimensions and all original nonnegative coreset weights
remain included. The proof imports RA06 **definitions**, not its final
sampler-specific negative theorem, and never substitutes Bernoulli weights for
arbitrary coreset weights. No proof depends on Challenge, a missing lower-bound
obstruction, a custom axiom, `sorry`, native execution or an external informal
theorem.

This faithfully formalizes Part I's necessary hyperplane tests, retaining the
original RA-05 model and its published attribution. It does not prove lower
support rates, the `2 < p < 3` graph-rate consequence mentioned in the contract,
or either full RA-05 answer. Legal hyperplanes at rank `d - 1` are a support
construction, not a replacement for the original arbitrary-rank target.
Canonical status remains Solved and all IDs and originals remain retained.

Reproduce this independent replay with:

```bash
python3 reviews/2026-10-23-solved-lean/ra05/verification/inventory-review/run_review.py \
  --lean /private/tmp/nla-oct23-lean-runtime/lean-4.33.1-darwin_aarch64/bin/lean \
  --packages /Users/ajt253/.codex/worktrees/pf05-lean-proof/OpenProblemsInNLA/nonnegative-and-positive-factorizations/PF-05/lean/.lake/packages
```

The replay reuses shared pinned compiled dependency caches. It is independent
source elaboration and theorem-trust checking, not a clean dependency rebuild,
Linux sandboxed Comparator receipt, CI result, source-author endorsement or
human review. Exact finite linear algebra and homogeneity require no numerical
interval certificate. A future canonical combined package must retain the
approved source hashes and explicitly incomplete full-target status.
