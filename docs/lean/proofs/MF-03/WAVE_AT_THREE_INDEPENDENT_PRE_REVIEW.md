# MF-03 value at three: independent pre-proof review

**Reviewer:** `/root`, 9 October 2026. **Verdict:** APPROVE the frozen `WAVE_AT_THREE_PRE_REVIEW.md` contract for implementation of its two exact numerical lemmas. This review does not approve or claim the all-order Padé target.

The proposed `waveAtThree` series is exactly `Σ_{j≥0} 3^j/(2j)!`. Direct rational checks give its first three terms as `1, 3/2, 3/8`, the `j=3` term as `3/80`, and the ratio from any `j≥3` as at most `3/56`. Thus the geometric tail bound is `21/530`, and `23/8+21/530=6179/2120`. The index `j=3` appears once in the tail, with no omitted term.

For every `m≥16`, the independently reviewed cosine-tail theorem yields `6*cosineTail m<1/24`, so the denominator is strictly greater than `23/24`. The proposed margin is exact: `(12177/6095)*(23/24)=4059/2120` and `12177/6095=2−13/6095`. Comparing the numerator upper bound with this positive multiple of the denominator proves the stated `≤` inequality without needing the numerator to be nonnegative. The denominator positivity is a proof obligation, not a hidden premise.

This numerical module still requires a genuine summability and infinite-tail argument. It does not identify the cosine product with the frozen Padé series, prove Schur denominator coefficients, construct all-order normalized pairs, or establish the frozen `Target`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`WAVE_AT_THREE_PRE_REVIEW.md`** | **`1657b281781deb6d186ace017cffa0aef34c38de42e669cbf8fa0339ace3b2c4`** |
| Frozen `NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| Reviewed `NLA/Proofs/MF03/CosineTail.lean` | `41fc5b7da2f1033b17608a56507aeeba555099f933a1b5eea05477331e8ace8b` |

Changed contract or source bytes reopen this pre-proof review.
