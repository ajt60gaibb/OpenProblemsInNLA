# TR-21 independent Lean boundary review

Reviewer: OpenAI Codex AI agent `/root/infrastructure`, 2026-10-09. I did not author the specification, live Lean module, or frozen copy. Phase: `lean-boundary`. Verdict: **APPROVE** the exact statement boundary. This review does not claim a proof of TR-21 or an isolated Linux Comparator run.

## Complete `check.py` review inputs

These are the SHA-256 hashes of `tools/lean_statements/check.py`'s `review_inputs` for the `lean-boundary` phase, including the complete repository-local import closure and all three pins.

| Input | SHA-256 |
| --- | --- |
| `tensor-computations/TR-21/README.md` | `645fab1674f258c7d120c880118f296ab2066b25ddd257e55bd5b1ad2e84e764` |
| `docs/lean/statements/TR-21/ORIGINAL.md` | `645fab1674f258c7d120c880118f296ab2066b25ddd257e55bd5b1ad2e84e764` |
| `docs/lean/statements/TR-21/NUMERICAL_TARGETS.md` | `8f8266b6106deb2648aacc0ffc6f50801d49c076d5c4638897d5d6606a39f0f4` |
| `lean-statements/NLA/Statements/TR21.lean` | `644b7114867561994a952f0ad4915717642ccc49697bb1d806da6c8192c9fab6` |
| `lean-statements/Reviewed/TR21.lean` | `8b3d64c62dec8066b06256e47fbedf86bd0042bbcbd087a9e8fc75a39be0979a` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

The live module imports only the local `NLA.Statements.Infrastructure` module in addition to pinned Mathlib and LeanCert. The frozen module differs by its prescribed leading comment and namespace substitution; I found no other mathematical change. The manifest pins LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` under Lean 4.33.1.

## Semantic comparison

`TensorIndex` is the dependent product of one finite coordinate per mode, and `Tensor` assigns a real entry to every such tuple. The target guards `r ≥ 3` and every `n_j ≥ 2`, covering all rectangular formats. `UnitVectors` fixes the squared real Euclidean norm to one separately in each mode. `Contraction` takes the full finite product of selected coordinates and sums it against every tensor entry. `InjectiveNorm` takes the absolute value of this full contraction, then `sSup` over all unit-vector tuples. In the guarded dimensions, the feasible set is nonempty and bounded, so this is the actual injective norm.

`FiberNorm` varies coordinate `j` with `Function.update` while all other coordinates remain fixed. Enumerating full indices repeats some fibers but omits none, so `FiberMaximum` is exactly the samplewise maximum over mode-`j` fibers. `FiberScale` integrates each samplewise fiber maximum under the entry product law and only then takes `sSup` across modes. In the guarded domain this is a finite maximum. It does not interchange expectation with either maximum.

`AdmissibleLaw` requires a probability measure, integrability of the real identity map (finite first absolute moment), and zero integral. `Measure.pi` forms the product of that same law over the complete finite tensor index. There is no extra variance, density, symmetry, or tail condition. The target chooses `c,C` after `r` and before every format and entry law, requires `0 < c ≤ C`, and states both non-strict comparisons. The separately named manuscript assertion keeps its stronger lower coefficient one. The distribution can vary with the dimensions; zero and heavy-tailed integrable laws remain included. No opaque semantic predicate replaces a norm, fiber, law, or expectation.

## Local checks and limits

I ran the pinned Lean 4.33.1 `lake build NLA.Statements.TR21 Reviewed.TR21`: **PASS**, 2491 jobs. Both modules executed `#assert_statement` and `#assert_trust kernel` for the principal and companion declarations. The target's printed transitive axioms were exactly `propext`, `Classical.choice`, `Quot.sound`. No local source in the import closure supplies a proof of the conjecture; a frozen statement identity and local macOS elaboration do not establish its truth or substitute for the CI Linux Comparator check.
