# FR-10 independent Lean boundary review

**Verdict: APPROVE.** I independently compared the live and frozen FR-10 Lean definitions, their complete repository-local import closure, the exact specification, the canonical page, and the dependency pins. This approves the statement boundary only. It does not prove `Target` or the companion manuscript bound.

## Reviewed inputs

The following are all nine paths returned by `tools/lean_statements/check.py review_inputs(..., "lean-boundary")` for FR-10. SHA-256:

| Input | SHA-256 |
| --- | --- |
| `frames-and-matrix-designs/FR-10/README.md` | `6e7f8ddb900da1cef486a6196c3ac277e79c7d0c953099b0e27441efea569e44` |
| `docs/lean/statements/FR-10/ORIGINAL.md` | `6e7f8ddb900da1cef486a6196c3ac277e79c7d0c953099b0e27441efea569e44` |
| `docs/lean/statements/FR-10/NUMERICAL_TARGETS.md` | `4302bb580024b66b0bdc7e65e493eefdba2ae33659c7181757f5965aea85cad3` |
| `lean-statements/NLA/Statements/FR10.lean` | `001753ea5a5560ab962558f5030e20108bb1d4b322c3d98f46397787afe09b92` |
| `lean-statements/Reviewed/FR10.lean` | `78aa805bc9cc5b4c386e1e0387d93a559991d85cc0bc4183fe56522f034fcbf3` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |

The canonical README and `ORIGINAL.md` remain byte-identical. The resolution manuscript previously checked against the specification is `references/haidary-resolutions-2026-09-30/Walsh_RIP_with_replacement_revised.tex`, SHA-256 `634946e8576c0c7f41fda7e18e2e5f55e6aec9dbaaaf8aaffc2018ca7b84d22e`.

## Semantic comparison

`Index d = Fin d → ZMod 2` has `2^d` elements. For each coordinate the canonical residue is `0` or `1`, so `(-1)^(∑ⱼ (a j).val * (b j).val)` is exactly the Walsh character determined by the `𝔽₂` dot product. `Sparse` counts precisely the nonzero real coordinates. `vectorEnergy` and `sampledEnergy` use the original real squared Euclidean norms; the latter divides the unnormalized sampled Walsh energy by positive `m` on every admissible input, exactly canceling the source's two square-root scale factors.

`RIP` quantifies over **all** real vectors of support at most `k` for one ordered sample and conjoins both weak bounds with coefficients `1/2` and `3/2`. `successProbability` counts all ordered functions `Fin m → Index d` satisfying that event and divides by `(2^d)^m`. This is the exact finite iid uniform law with replacement, retaining repeated rows and samples larger than `N`; no random-event approximation or exhaustive numerical evaluation occurs in the proposition.

`Qualifies` uses positive `m` and inclusive `9/10`. `mStar` is the set infimum, while the first conjunct of `Target` explicitly requires that it qualify and be least for every `d ≥ 1` and `1 ≤ k ≤ 2^d`. Therefore the empty-set value of `sInf` cannot satisfy the target. The next conjunct states `mStar(d,1)=1`. The final conjunct places the positive constants outside both the dimension and sparsity quantifiers, and covers `2 ≤ k ≤ 2^d`, including `d=1`, `k=N`, and the dense regime. `Rate` is exactly `k log(2k) log(2e·2^d/k)` over the reals with natural logarithms and `e=exp(1)`.

The separate `ManuscriptQuantitativeBound` preserves the source's stronger coefficient `1/2000`, while `Target` retains the original existential lower coefficient. It does not replace or omit any original question. No opaque proposition parameter, algorithm oracle, sorry, or unreviewed local definition hides part of the target. The only repository-local import is `NLA.Statements.Infrastructure`, whose assertion command checks a safe closed `Prop` definition and its transitive axioms. The manifest pins Lean 4.33.1, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`, and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

The frozen file differs from the live file only in its header and namespace names. The frozen proposition has the same definitions and signatures. The final Comparator identity check remains a separate execution gate.

## Local check

`lake build NLA.Statements.FR10 Reviewed.FR10` completed successfully using the pinned Lean 4.33.1 Darwin toolchain and the available dependency cache. Both modules report only `propext`, `Classical.choice`, and `Quot.sound` for `Target`. This local build does not claim an isolated Linux Comparator run or a proof of the Walsh sampling theorem.
