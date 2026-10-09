# IE-08 independent Lean-boundary review

**Verdict: APPROVE.** Reviewer: `/root`, 2026-10-09. I did not author the IE-08 live or frozen Lean boundary or its machine module. This reviews an exact problem statement and its computational model; it does not prove that the requested algorithm exists.

I compared the complete canonical README, the source solution's computational-model paragraph, the reviewed numerical target, the finite-machine semantics, and both Lean boundaries. `Program` is finite code with finite registers and fixed rational literals. Its only matrix-input instruction rounds one real component into a binary float at the selected precision. The real arithmetic instructions round each result; comparisons inspect only stored floats; randomness reads finitely many unbiased bits. There is no exact input, eigensolver, Gaussian, matrix-function, or arbitrary-precision arithmetic instruction. The exact `Real.log` and `Int.floor` inside `round` specify one floating-point primitive's rounding semantics and are unavailable as program instructions. Natural-register arithmetic and memory access are explicit transitions with a bit-length-dependent charge.

Every stored real component must fit the selected `p`-bit mantissa, including on unsuccessful runs. A program could combine multiple such words by executing ordinary finite instructions, but this is charged as a sequence of operations; the source excludes multiword precision *as a primitive*. The canonical resource promise is per real component and a total arithmetic-operation cap. The finite step charge includes mantissa and natural-register/address widths, which are absorbable into a universal polylogarithmic exponent for the source algorithm. An earlier draft charged the binary length of floating-point exponents; that would falsely reject arbitrarily tiny legal inputs. The reviewed machine instead uses the source's sufficiently wide exponent range and unit-cost floating-point operations. Exponents are not directly readable into natural registers or significands; any operation involving them still uses a finite instruction.

The dyadic request exponent is the machine's only tolerance input; `AccuracyBridge` and `AccuracyEncoding` make every real `0<δ<1/2` available within a factor of two, while the work and precision caps remain functions of the original `δ`. `Target` quantifies one program and universal constants across every positive dimension and every complex input of spectral norm at most one. `RunOK` requires termination and the capped work and mantissa use for every finite bit tape, plus exact stored upper triangularity of `T`, including unsuccessful paths. `Successful` measures both original spectral-norm residuals against the exact original matrix in the same run, and `successProbability` is the uniform finite-bit fraction with threshold `99/100`. No gap, diagonalizability, simplicity, or good-input hypothesis has been inserted.

I independently ran the pinned live/frozen build and `Target = Reviewed.Target := by rfl` after the exponent-cost correction; both passed. LeanCert kernel trust found only standard logical axioms (`propext`, choice, and `Quot.sound`). The equivalence of this finite-code machine's cost conventions to the source's asymptotic floating-point model is a mathematical/computational review judgment, not a Lean theorem. In particular this is a statement-only boundary and supplies no program or proof of its guarantee.

## SHA-256 review inputs

| Path | SHA-256 |
| --- | --- |
| `docs/lean/statements/IE-08/NUMERICAL_TARGETS.md` | `31b774bae370d55c6575397db6c4b3dbad447a9205f3ab2549a96fd85b2bba08` |
| `docs/lean/statements/IE-08/ORIGINAL.md` | `22dd77f1baaa4004bb8c05ec34c63bffabf99103d48ecfb9fcec92d1bdcc4e7d` |
| `eigenvalues-and-inverse-problems/IE-08/README.md` | `22dd77f1baaa4004bb8c05ec34c63bffabf99103d48ecfb9fcec92d1bdcc4e7d` |
| `eigenvalues-and-inverse-problems/IE-08/solution.md` | `650053dc10070ada37746a7fbb5a0d4735de967cc4452d5d03f771216a3e379d` |
| `lean-statements/NLA/Computation/FiniteFloatMachine.lean` | `ed8498796c2f135ccf08399fdabd073a48c8777727229b22b924780080b20d6b` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `lean-statements/NLA/Statements/IE08.lean` | `a17c0c7a81d585a6dcdd9bef0cc307e5665a8101b29fe1f2d498d3de3e353759` |
| `lean-statements/Reviewed/IE08.lean` | `3e174a6ec243d052f4f034266b5651fc1dcdc0c43979f5386d9e208f4289ede7` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
