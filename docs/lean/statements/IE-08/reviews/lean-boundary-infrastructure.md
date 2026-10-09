# IE-08 independent Lean boundary review

Reviewer: OpenAI Codex AI agent `/root/infrastructure`, 2026-10-09. I did not author the IE-08 specification, finite machine, live statement, or frozen statement. Phase: `lean-boundary`. Verdict: **APPROVE** for this exact statement boundary. This is a review of the proposition, not a proof that the requested algorithm exists.

## Exact `check.py` review inputs

| Input | SHA-256 |
| --- | --- |
| `docs/lean/statements/IE-08/NUMERICAL_TARGETS.md` | `31b774bae370d55c6575397db6c4b3dbad447a9205f3ab2549a96fd85b2bba08` |
| `docs/lean/statements/IE-08/ORIGINAL.md` | `22dd77f1baaa4004bb8c05ec34c63bffabf99103d48ecfb9fcec92d1bdcc4e7d` |
| `eigenvalues-and-inverse-problems/IE-08/README.md` | `22dd77f1baaa4004bb8c05ec34c63bffabf99103d48ecfb9fcec92d1bdcc4e7d` |
| `lean-statements/NLA/Computation/FiniteFloatMachine.lean` | `ed8498796c2f135ccf08399fdabd073a48c8777727229b22b924780080b20d6b` |
| `lean-statements/NLA/Statements/IE08.lean` | `a17c0c7a81d585a6dcdd9bef0cc307e5665a8101b29fe1f2d498d3de3e353759` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `lean-statements/Reviewed/IE08.lean` | `3e174a6ec243d052f4f034266b5651fc1dcdc0c43979f5386d9e208f4289ede7` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |

These are all ten paths returned by `tools/lean_statements/check.py` `review_inputs` for IE-08's `lean-boundary` phase. The source solution's computational-model paragraph was also checked: `eigenvalues-and-inverse-problems/IE-08/solution.md` has SHA-256 `650053dc10070ada37746a7fbb5a0d4735de967cc4452d5d03f771216a3e379d`. `ORIGINAL.md` is byte identical to the canonical README.

## Semantic comparison

`Program` is one finite instruction table with fixed rational literals and finitely many registers, quantified outside every input. The only instruction reading the mathematical matrix returns one row-major real or imaginary component rounded to the selected `p`-bit binary float. No instruction exposes the exact input, an eigensolver, a Gaussian oracle, or an exact-real arithmetic branch. Every real arithmetic instruction rounds its result; real comparisons inspect stored floats; the fixed `round` rule itself is semantic hardware behavior, not a callable exact-logarithm instruction. Precision is selected once, and `RunOK` bounds the mantissa of every live register and every memory address on every run. `RoundedPrimitiveCorrect` explicitly states the ordinary relative error bound for this concrete round rule. For negative half ties it rounds toward positive infinity; a carry can occur only at an even signed significand, so normalization preserves the rounded value and the `p`-bit bound.

I initially objected to an earlier version that charged the binary length of the exponent. For arbitrarily tiny legal inputs this made the uniform cost bound false. The reviewed revision removes that charge and uses the source's unrestricted exponent range. It still charges each instruction, selected mantissa width, natural-register lengths, and accessed memory mantissas. There is no instruction exposing exponent bits or treating an exponent as a significand. A programmed multiword routine would use these finite instructions and incur their costs; there is no free multiword primitive. Since every running step costs at least one, the worst-case cost cap implies the canonical arithmetic-operation count bound. The additional finite bit-work charges fit within the universal polylogarithmic exponent of the approved computational specification.

The dyadic request exponent is the machine's only accuracy input. `AccuracyBridge` covers every real `0 < δ < 1/2`, and `Target` covers every valid dyadic encoding while keeping work and precision caps in the original `δ`. The target quantifies every `n ≥ 1` and every complex matrix of true induced spectral norm at most one, with no spectral separation or diagonalizability assumption. `RunOK` requires a halt, cost and precision caps, and exactly upper triangular stored `T` on **every** finite bit tape, including unsuccessful paths. `Successful` tests both weak spectral-norm residuals against the original exact matrix on the **same** run. The finite uniform fraction of successful tapes is at least the exact rational `99/100`.

## Pinned kernel and identity checks

With the pinned Lean 4.33.1 toolchain, `lake build NLA.Statements.IE08 Reviewed.IE08` passed (8711 jobs). Both `#assert_statement` and `#assert_trust kernel` passed; each printed axiom closure is `propext`, `choice`, and `Quot.sound`. A fresh file importing both modules proved

```lean
example : NLA.Statements.IE08.Target = NLA.ReviewedStatements.IE08.Target := by rfl
```

The frozen mathematical body is exactly the live body after the documented namespace substitution and header. No IE-08 Lean file was edited during this independent review. The finite-machine cost equivalence to the source's asymptotic floating-point model is a semantic review judgment, not a Lean theorem.
