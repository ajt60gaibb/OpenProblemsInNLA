# MF-03 value at three and numerical margin: independent Lean source review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE frozen `WaveAtThree.lean` as a kernel-checked proof of the two exact numerical theorems approved before implementation. This does not prove the cosine-product link, Padé existence, denominator coefficient estimates, disk bound, or full all-order MF-03 `Target`.

The public `waveAtThree` is exactly the real infinite sum `Σ_{j≥0}3^j/(2j)!`, matching the manuscript's `f(3)`. The source proves summability through the real hyperbolic-cosine series at `√3` and `(√3)²=3`. Its exact factorial recurrence gives `a_(j+1)=a_j·3/[(2j+2)(2j+1)]`. For `j≥3`, the denominator is at least `56` and all terms are nonnegative, so induction bounds `a_(3+k)≤(3/80)(3/56)^k`. The tail is compared as a genuine infinite sum with the geometric sum `21/530`; the first three terms sum to `23/8`. Thus the exported theorem is precisely `waveAtThree≤6179/2120`, including equality-allowed weak direction. No finite truncation or decimal estimate is substituted for the infinite tail.

For every natural `m≥16`, the separately reviewed `cosineTail m<1/(9m)` yields `6*cosineTail m<1/24`, so `1−6*cosineTail m>23/24>0`. The source proves this denominator positivity before division. It combines the exact value bound with `(2−13/6095)·(23/24)=6179/2120−1` to prove the elaborated conclusion

```text
(waveAtThree−1)/(1−6*cosineTail m) ≤ 2−13/6095.
```

The margin `13/6095>0` is exact and implies a strict bound below two. The theorem contains the actual `cosineTail m` and no unconstrained surrogate, while the product-to-Padé bridge remains unproved.

Pinned `lake build NLA.Proofs.MF03.WaveAtThree` and a separate imported audit of both elaborated signatures, `#assert_trust kernel`, and `#print axioms` passed under Lean 4.33.1. Each theorem's transitive axioms are exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/MF03/WaveAtThree.lean`** | **`824320b42ef6c052c12f6e68ebfb774a4ed969544a70f32a47cd0d8102682b6a`** |
| `lean-statements/NLA/Proofs/MF03/CosineTail.lean` | `41fc5b7da2f1033b17608a56507aeeba555099f933a1b5eea05477331e8ace8b` |
| `WAVE_AT_THREE_PRE_REVIEW.md` | `1657b281781deb6d186ace017cffa0aef34c38de42e669cbf8fa0339ace3b2c4` |
| `WAVE_AT_THREE_INDEPENDENT_PRE_REVIEW.md` | `481e73e0fa657ba65da7c549dd51509c2a63672d2271738e4c306da9af5f25ba` |
| Frozen `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| Independent `/private/tmp/mf03-waveatthree-independent-audit.lean` | `56fcc1f34a27978f7088ba862d0c53369cbb802e5ce52445335b170c37c66cde` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

Changed source or approved contract bytes reopen this review.
