# MI-21 statement freeze — stage 1

The explicit statement-only build `lake build NLA.MI21.Definitions Challenge` passed (2710 jobs), with only the three intentional Challenge placeholders. No proof implementation or Solution exists. The actual complete universal target, true CFC definitions and true Euclidean operator norm are ready for two independent statement reviews. No theorem is assumed from the manuscript.

| File | SHA256 |
|---|---|
| `NLA/MI21/Definitions.lean` | `18ebd6d65063b6e970d76b60aab6a8a8bc595189e9b8e188895030d2172f1055` |
| `Challenge.lean` | `f7dd628a7635e8860dec64460bd53adfa71ca391eec763391ae1c8e58d1588b4` |
| `NUMERICAL_TARGETS.md` | `4b0582a3c2da02abf7a349e4ab4af682f6b29bf7026bff21d53edff3ab216312` |
| `SOURCE_MAPPING.md` | `1aa408ef570bb889a8aeddf1fca0574f59384d6ebafaa9aed217a7d31e24fed2` |
| `lakefile.toml` | `6e951e8df2455129ae6095b75af2766b92fa8ef686ac165fd690edb53122f640` |
| `lake-manifest.json` | `5295b0daacfbde17ca15d1746b2bcae5576725c446e38c2b67822c718458bee9` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `comparator.json` | `e2f703dcc0f1cd3f4b3bdf725b8d918d2f68d61324197817e39a970e80cc7bc3` |

The [statement build record](../verification/statement-build.json) includes actual toolchain/dependency pins and the log hash. [Numerical sanity checks](../verification/numerical-statement-check.json) confirmed the rational matrices, both scaled Riccati identities and the strict gap before Lean proof work; these are not claimed as Lean certificates. The original failed typecheck is retained separately; it required only opening the matrix notation namespace and making the Euclidean-operator-norm type parameters explicit, before this freeze.

Review especially the all-unitarily-invariant-norm quantifier and its complete norm axioms; actual CFC powers and noncommuting factor order; positive definiteness of the actual complex inputs; real parameter restrictions; true operator norm admissibility; and the strict witness's implication for the entire universal claim. Source and formalization authors remain separately attributed. No canonical status, problem ID, proof, commit or push was changed.
