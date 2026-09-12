# MI-19 statement-review request

**Stage 1 only.** No solution proof or canonical status change has been made. The definitions, complete target declarations, and exact numerical obligations are ready for root and independent statement-referee review before proof implementation.

Base revision: `5adea969c17391693978ada2674d25bb5c3daeb1`. Toolchain and all dependency revisions are pinned in the package manifest. The actual local dependency HEADs were checked against those pins.

## Build evidence

`lake build NLA.MI19.Definitions Challenge` exited 0 with `Build completed successfully (2159 jobs).` The only warnings are the two deliberate Challenge placeholders. The successful output is in `statement-build.log`. An earlier unsuccessful elaboration log is retained separately: it was fixed by importing Complex.Basic rather than abstract RCLike.Basic and making the preservation predicate transparent to finite decidability. No mathematical theorem was added as a premise.

## Review focus

- Arbitrary complex Hermitian PSD inputs are represented by `Matrix.PosSemidef`; no entrywise-positive, real-only, or invertibility restriction is inserted.
- The full ordering supplies inversion counts in both sums. The subset predicate means setwise preservation for all nonempty proper subsets; the paper's interior singleton {2} becomes Fin4 index1.
- Complex order means ordered real parts and equal imaginary parts. The witness export additionally proves both sums have zero imaginary parts, so the counterexample does not exploit incomparable complex values.
- The exact gap is the gap of the actual finite permutation sums. No assumed polynomial or external calculator result replaces them.
- The universal-negation export must follow from the complete admissible strict witness.
- The Challenge module contains the only placeholders and must never be imported by Solution. A successful statement build is not a proof claim.

## Frozen statement hashes

| File | SHA-256 |
| --- | --- |
| `NUMERICAL_TARGETS.md` | `cd93a4cefb529b69755c10bae600718442e0e6b8749c37df87c6dabec9b751aa` |
| `NLA/MI19/Definitions.lean` | `170e406d1f6bf0ca60e5b65998308b030cf08cc0def51c25c9860524ad3441ac` |
| `Challenge.lean` | `9c838a34cbff20eceb5e842eeca77c310bccb442843925343a7827a1020063cb` |

All source and config hashes, the toolchain identity, and the successful statement-build scope are recorded in `statement-freeze.json`. The independently reconstructed rational precheck agrees with the manuscript but is not trusted by the eventual Lean proof.
