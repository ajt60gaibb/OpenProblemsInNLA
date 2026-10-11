# RA-06 asymptotic arithmetic: independent review

**Historical scope:** This reviews the earlier `Asymptotic.lean` hash below.
The current generalized source is reviewed in
[`SAMPLING_ASYMPTOTIC_INDEPENDENT_REVIEW.md`](SAMPLING_ASYMPTOTIC_INDEPENDENT_REVIEW.md).

This is a source-level and local kernel review of the conditional numerical
module. It does not certify a proof of the complete RA-06 `Target`.

## Reviewed inputs (SHA-256)

| Input | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-06/README.md` | `5ee10eb6d467ef6ebbd56955cdc95b2a1ff0613231d7e5ed6814679491d78f98` |
| `docs/lean/statements/RA-06/NUMERICAL_TARGETS.md` | `7036e298c8f74c4693fb638daf1aa22778756a9c26c53fbc39a9341e85f3d5e8` |
| `references/haidary-resolutions-2026-09-30/ra06-counterexample-revised.tex` | `21c5187b695e4469d803ceced320bd0314ade4702ed4567160f8ff835122cec7` |
| `lean-statements/NLA/Statements/RA06.lean` | `865af15803905e04de1202266f5af75fc5486b8345fdba25a44052202742883d` |
| `lean-statements/NLA/Proofs/RA06/Basic.lean` | `e395d2efe229ee011b1f1ceaae748b6b25e16521f10be81bf756318a34d11661` |
| `lean-statements/NLA/Proofs/RA06/Asymptotic.lean` | `c00bbdd912c104498a8d1e4d19a08d80a155c24bd1c4c2308a292c5d993c4988` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

## Exact target alignment

The canonical assertion has arbitrary real `p > 2`, positive constants `C,c`
chosen before the matrix and tolerances, budget
`C * ε⁻² * (TotalSensitivity A p + d) * log(2*n*d/(ε*δ))^c`, and success for
the same sampling parameter. The resolved target negates that assertion for
every `p > 2`. The manuscript's counterexample uses `b ≥ 3`, `ε = 1/b`,
`δ = 1/4`, `v = ⌈b^(p+2)⌉`, `n = v(v−1)/2`, and `d = v−1`.

`exists_large_accuracy_parameter` proves, for every such `p,C,c`, a natural
`b ≥ 3` with the **strict** separation

```text
C*(2^(p−2)+1)*log(32*b^(3*p+7))^c
    < (6^(−p)/3)*b^(p−2).
```

The coefficient, logarithm argument, and exponent agree with the manuscript's
final contradiction. `accuracy_parameter_dimension_regime` proves the exact
real inequality `6^(−p)*b^(p+1)+1 ≤ b^(p+2)` for `b ≥ 3`; with the ceiling
definition this supplies `v−1 ≥ 6^(−p)*ε^(−(p+1))`. The ceiling transfer itself
is outside this module.

`finite_bounds_contradict_power_log_separation` is a valid conditional
contradiction. Its `S` must be instantiated as **the complete**
`TotalSensitivity A_v p + (d : ℝ)`, and its `E` as
`ExpectedSize A_v p α`. The required hypotheses are explicitly present:
`S ≤ (2^(p−2)+1)*v`, `(6^(−p)/3)*v*b^p ≤ E`, and
`E ≤ C*b²*S*log(32*b^(3*p+7))^c`. The proof scales the sensitivity bound by a
nonnegative factor and the strict separation by positive `v*b²`; it uses
`b^p = b^(p−2)*b²`. There is no concealed replacement of `S+d` by `S`.
The finite theorem omits `0<c` because its supplied strict separation is the
only fact about `c` needed at this stage; the logarithm power is nonnegative
for any real `c` here. The positive `c` from the original claim is used when
obtaining that separation and bounding the logarithm. This does not weaken
the conditional inference.

## Kernel result and remaining bridges

From `lean-statements`, both `lake build NLA.Proofs.RA06.Asymptotic` and the
direct command `lake env lean NLA/Proofs/RA06/Asymptotic.lean` passed with
Lean `v4.33.1`, Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`,
and LeanCert commit `621a43d7cf21f87872392a01e874f2f1dbddc926`. The
source sets `leancert.trust "kernel"` and executes `#assert_trust kernel` on
all four exports. Direct `#print axioms` reported only `propext`,
`Classical.choice`, and `Quot.sound` for each. I found no `sorry`, custom
axiom, `unsafe`, `native_decide`, or numerical certificate in this module.

The full RA-06 proof still needs to derive the sensitivity and expected-size
bounds for the actual incidence matrix and **same** `α`, obtain the lower
bound from positive success probability and existence of one successful
outcome, transfer the ceiling dimension regime, and turn the raw budget's
`log(8*b*n*d)^c` into the bounded logarithm. For the last step the manuscript
uses `v ≤ 2*b^(p+2)` and `8*b*n*d ≤ 4*b*v³ ≤ 32*b^(3*p+7)`, with `c>0`.
Those premises are visible interfaces, not theorems of this module. This
review therefore approves its conditional arithmetic only. It is not a
Linux Comparator result or certification of `NLA.Statements.RA06.Target`.
