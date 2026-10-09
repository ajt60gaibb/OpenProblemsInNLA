# RA-06 final proof: independent mathematical and kernel review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE the frozen `NLA.Proofs.RA06.target` as an exact local Lean proof of `NLA.Statements.RA06.Target`. The proof passed an independent LeanCert kernel audit with only the three standard axioms. This is a mathematical/source review and local build result; it is not a fresh isolated Linux Comparator receipt.

## Exact target and quantifiers

I compared `Final.lean` with the permanent RA-06 README, the frozen `RA06.lean` target, the [pre-proof statement review](STATEMENT_REVIEW.md), and the source manuscript. The theorem's elaborated type is **literally** `NLA.Statements.RA06.Target`; a separate audit also elaborated `example : NLA.Statements.RA06.Target := NLA.Proofs.RA06.target`. That target is `∀ p : ℝ, 2 < p → ¬ OriginalPositiveClaim p`. The original positive claim chooses positive **real** `C,c` after fixing arbitrary real `p>2`, then requires one positive `α` for every full-column-rank matrix and every `ε,δ∈(0,1/2)`. The same `α` must satisfy both the expected-size budget and success probability at least `1−δ` for the exact independent sampler.

The proof assumes an arbitrary proposed `C,c` and selects an integer `b≥3` from the power-over-polylog separation. It sets `ε=1/b`, `δ=1/4`, `v=⌈b^(p+2)⌉`, `d=v−1`, `n=card (Edge v)`, and `A=GraphMatrix d`. The grounded complete-graph incidence matrix has the prescribed row count and full column rank. The positive claim supplies **one** `α` together with both `hbudget` and `hsuccess`; neither is replaced by a different sampler, a chosen successful outcome, or a fixed exponent. The final contradiction is derived for this very `α`, so the negation covers every proposed `C,c` and every real `p>2`.

## Mathematical and numerical chain

The existing independently reviewed `GraphWitness.lean` and `GraphFinite.lean` establish the arbitrary-nonnegative-weight graph obstruction, its exact retained-row specialization, and the finite Bernoulli expectation transfer. `Final.lean` invokes the latter with the actual `Embedding (GraphMatrix d) p α ε` and the actual success probability from the frozen statement. The sample weights are reciprocal **original** probabilities `min(1,1/n+s_i/α)`, so the `1/n` floor, cap at one, and row rescaling are retained. Every vector is quantified in the embedding-to-graph bridge. The probability transfer keeps the factor `1−δ`, rather than inferring an expectation bound from existence of a single successful outcome.

For the chosen `δ=1/4`, the exact lower estimate is

```text
E ≥ (3/4) * (v/2) * (6/b)^(−p)
  = ((3/8) * 6^(−p)) * v * b^p.
```

The power identity uses `b>0`; no floating-point evaluation or unproved approximation appears. `dimension_regime_for_ceiling` derives `(6/b)^(−p)≤(v−1)/b` from the exact ceiling and `b≥3`, justifying the finite support theorem's regime. The sensitivity route uses the safe bound

```text
S = TotalSensitivity A p + d ≤ K*v,
K = 2*2^(p−1)+1 > 0.
```

This `K` is coarser than the source's sharper `2^(p−2)+1`, but it is a proved upper bound and remains independent of `b,v,α`. Similarly, the expectation lower bound has the explicit `3/4` factor, which is weaker than the source's common-probability corollary but still suffices for the unchanged target.

The budget is used with its **raw** logarithm `log(2*n*d/(ε*δ))`. The ceiling and coarse graph counts give `n≤v²`, `d≤v`, and `v≤1+b^(p+2)≤(3/2)b^(p+2)`, hence the exact numeric upper bound

```text
2*n*d/((1/b)*(1/4)) = 8*b*n*d
                         ≤ 27*b^(3p+7) ≤ 32*b^(3p+7).
```

The proof establishes that the original logarithm is nonnegative before raising it to the arbitrary positive real exponent `c`. It also rewrites `(1/b)^(−2)=b²` exactly and uses `S≥0`. Thus the proposed budget gives

```text
E ≤ C*b²*S*(log(32*b^(3p+7)))^c
  ≤ C*K*v*b²*(log(32*b^(3p+7)))^c.
```

The independent asymptotic lemma chooses `b` so that `C*K*(log(32*b^(3p+7)))^c < L*b^(p−2)` with `L=(3/8)*6^(−p)>0`. Multiplying by `v*b²>0` strictly separates the preceding upper estimate from `E≥L*v*b^p`; `finite_bounds_contradict_for_coefficients` closes the contradiction. The constants `K,L` may depend on fixed `p`, while `b` may depend on `p,C,c`, exactly as the negation permits. The proof never constrains the original positive claim to a fixed matrix family in its statement; the graph is the counterexample supplied after arbitrary constants are assumed.

## Trust check and source scan

Using the project's pinned Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`, I ran `lake build NLA.Proofs.RA06.Final`, direct `lake env lean NLA/Proofs/RA06/Final.lean`, and `lake env lean /private/tmp/ra06-final-independent-audit.lean`. All exited zero after other concurrent Lake builds in the shared checkout finished. The separate audit checks that `NLA.Proofs.RA06.target` is a `.thmInfo` proof constant, elaborates an exact `Target` example, runs `#assert_trust kernel`, and prints its transitive axioms: **only** `[propext, Classical.choice, Quot.sound]`. The final module itself also contains `#assert_trust kernel target` and the same axiom print. A scan of all `NLA/Proofs/RA06/*.lean` and the proof aggregator found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` token.

The proof aggregator `NLA/Proofs.lean` now imports `Final.lean` and asserts LeanCert kernel trust for `NLA.Proofs.RA06.target`; I independently elaborated that updated aggregator successfully. A fresh isolated Linux Comparator/LeanCert receipt has not been reviewed here.

## SHA-256 of reviewed inputs

| Input | SHA-256 |
| --- | --- |
| Canonical `RA-06/README.md` | `5ee10eb6d467ef6ebbd56955cdc95b2a1ff0613231d7e5ed6814679491d78f98` |
| Resolution source `ra06-counterexample-revised.tex` | `21c5187b695e4469d803ceced320bd0314ade4702ed4567160f8ff835122cec7` |
| Frozen `NLA/Statements/RA06.lean` | `865af15803905e04de1202266f5af75fc5486b8345fdba25a44052202742883d` |
| `NLA/Proofs/RA06/GraphWitness.lean` | `cc1ded7324a6520ba901727bd0c7bce046b6f34bbc8b76906f152624902d5cd6` |
| `NLA/Proofs/RA06/GraphFinite.lean` | `65012435863c6302c5bf82efcca4617d50edbf75c0a921f88528dc673301e70b` |
| `NLA/Proofs/RA06/Asymptotic.lean` | `4d39acee6e037a457445f6908bc16c82a40bed299fd15061f6df92eb7fe5d8f1` |
| **`NLA/Proofs/RA06/Final.lean`** | **`54454fd6207fb55664d06d8c32ee9608c5089db08efa34d2d90716966c8b434c`** |
| `NLA/Proofs.lean` aggregator | `625d4ac1b89b3b83366a6f7c70b34c3a49c73c91a8ae1f540ef2dce15a0b41fe` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| Independent `/private/tmp/ra06-final-independent-audit.lean` | `f7c01008afdca0d8de09afb00ce68a33a4fb5c632df25f7c285983d4f8a8c381` |

Any changed mathematical source requires renewed review of the affected claim.
