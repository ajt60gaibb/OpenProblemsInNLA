# MF-03 large-order disk bridge: independent pre-review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen conditional mathematical/numerical contract for implementation. It is a disk consequence of a coefficient bound, not an all-order Padé existence proof or the frozen `Target`.

| Reviewed input | SHA-256 |
| --- | --- |
| `LARGE_ORDER_DISK_PRE_REVIEW.md` | `f9bf647e49d63c47fdbd14b10a7c00775164efc5cf6ae0c61b79c1a9dfdb847f` |
| Frozen `NLA.Statements.MF03` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| Audited `Disk.lean` | `c7ced478264defa6a8365df21c2cb3d861adc18c37d67c793c3336df14d7f53a` |
| Audited `CosineTail.lean` | `41fc5b7da2f1033b17608a56507aeeba555099f933a1b5eea05477331e8ace8b` |
| Audited `WaveAtThree.lean` | `824320b42ef6c052c12f6e68ebfb774a4ed969544a70f32a47cd0d8102682b6a` |

For `j≤m`, the frozen normalized Padé equation has precisely `P_j=Σ_{i=0}^j Q_i/(2(j−i))!`; subtracting its `i=j` term gives the displayed convolution over `i<j`, including the empty `j=0` case. The degree and normalization premises are already part of `NormalizedPadeRepresentation`. On the radius-three disk, the finite convolution and triangle inequality yield `N≤B(F(3)−1)` by rearranging nonnegative terms and bounding the truncated factorial tail by the full summable tail. This argument uses only the frozen factorial series, with no Euler-product identity.

The proposed coefficient hypothesis gives `T≤Σ_{j=1}^m(3S)^j≤3S/(1−3S)`. From the existing tail theorem and `m≥16`, `0≤6S<1/24`, hence `x=3S<1/48`, `T<1`, and `1−2x>0`. The algebraic identity behind `B/(1−T)≤1/(1−2x)` is `T(1−x)≤x`, exactly the geometric estimate; it uses `B=1+T`. The existing rational margin proves `(F(3)−1)/(1−6S)≤2−13/6095<2`. Multiplying by positive denominators yields the exact Disk lemma premise `N≤2(1−T)`, with room to spare. The conclusion covers every complex point with `‖z‖≤3`, including boundary points. No floating-point certificate enters.

The implementation may reprove the factorial-series nonnegativity, summability, and tail split in its own module. It must preserve the universal `j=1,…,m` coefficient hypothesis and the exact normalized pair equations. Existence of an all-order normalized pair with that bound, Schur/tableau coefficient identities, the product-to-series bridge, reduction, and the universal reduced-pair target remain separate proof obligations. Freeze the source unimported for a separate LeanCert kernel/signature audit.
