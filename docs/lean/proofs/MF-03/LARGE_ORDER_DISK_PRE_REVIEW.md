# MF-03 large-order disk bridge: pre-implementation contract

This contract proposes one conditional lemma for the `m ≥ 16` part of the
frozen `NLA.Statements.MF03.Target`. It is a request for independent
mathematical and Lean-interface review, not a proof or a change to the Target.

## Exact proposed theorem

In a new `NLA.Proofs.MF03.LargeOrderDisk` module, import the frozen MF-03
statement and the existing `Disk`, `CosineTail`, and `WaveAtThree` proof
modules. Export only the following theorem (helpers may be private):

```lean
theorem largeOrder_disk_of_tail_coefficients
    (m : ℕ) (hm : 16 ≤ m) (P Q : Polynomial ℂ)
    (hpair : NLA.Statements.MF03.NormalizedPadeRepresentation m P Q)
    (hcoeff : ∀ j : ℕ, 1 ≤ j → j ≤ m →
      ‖Q.coeff j‖ ≤ (cosineTail m) ^ j) :
    ∀ z : ℂ, ‖z‖ ≤ (3 : ℝ) →
      Q.eval z ≠ 0 ∧
        ‖(1 : ℂ) - P.eval z / Q.eval z‖ ≤ (2 : ℝ)
```

The coefficient hypothesis is exactly the norm consequence of the
manuscript's `Q_m(z)=∑_{j=0}^m(-1)^j b_(m,j)z^j` with
`0<b_(m,j)≤S_m^j`, where `S_m=cosineTail m`. It applies to one *normalized*
pair. The theorem does not assume or prove that such a pair exists. It also
does not assume the pair is reduced: the existing `normalized_exists_reduced`
and `disk_bound_for_every_reduced_pair` are the later route to the frozen
existence and universal reduced-pair clauses, once all-order normalized
existence and the coefficient estimate have been proved.

## Finite convolution and disk budget

Write `S=cosineTail m`, `x=3S`, `q_j=Q.coeff j`, and
`a_k=3^k/(2k)!`. From `hpair`, `q_0=1`, both degrees are at most `m`, and
for each `0≤j≤m` the exact frozen Padé coefficient equation gives

```text
P.coeff j - Q.coeff j
  = ∑_{i=0}^{j-1} q_i / (2(j-i))! .
```

The right side is empty for `j=0`. No infinite-product coefficient claim is
used here. Define the existing `Disk.lean` budgets

```text
T = ∑_{j=1}^m ‖q_j‖ 3^j,
B = 1+T = ∑_{j=0}^m ‖q_j‖ 3^j,
N = ∑_{j=0}^m ‖P.coeff j-Q.coeff j‖ 3^j.
```

The coefficient hypothesis and the finite geometric sum yield

```text
0 ≤ T ≤ ∑_{j=1}^m x^j ≤ x/(1-x).
```

The finite convolution, triangle inequality, nonnegative `a_k`, and
reindexing `j=i+k` yield

```text
N ≤ B ∑_{k=1}^∞ a_k = B (waveAtThree-1).
```

The last equality requires an actual summability and head/tail split of the
factorial series; it must not be inferred from an unproved product identity.
The `WaveAtThree.lean` module already establishes summability internally;
the new module can reprove the needed nonnegative-series helper locally
without editing that reviewed source. In particular, the series starts with
`a_0=1`, so `waveAtThree-1≥0`; this sign is needed when multiplying the
geometric comparison by the series tail.

For `m≥16`, positivity of each cosine factor gives `0≤S`, while the
`CosineTail.lean` bound gives
`6S<1/24`, so `0≤x<1/48<1/2` and `T<1`. The geometric bound implies the
exact algebraic comparison

```text
B/(1-T) ≤ 1/(1-2x) = 1/(1-6S).
```

Equivalently, `(1+T)(1-2x)≤1-T`; this is exactly
`T(1-x)≤x`. `WaveAtThree.largeOrder_numeric_margin` supplies

```text
(waveAtThree-1)/(1-6S) ≤ 2-13/6095 < 2.
```

Therefore `N≤2(1-T)`, the precise numerator budget required by the
already kernel-checked `disk_bound_of_coefficient_tail`. Its other premises
are the degree bounds, `q_0=1`, and `T<1`, all supplied above. That theorem
then proves nonvanishing and the error bound for *every* complex point in
the closed disk, including its boundary `‖z‖=3`.

## Scope and remaining all-order source obligation

This bridge is deliberately conditional. The largest missing theorem is
still, for every `m≥16`, existence of `P,Q` satisfying the *exact* frozen
normalized Padé equations and `‖Q.coeff j‖≤(cosineTail m)^j` for
`1≤j≤m`. The manuscript obtains this from the infinite cosine product,
elementary-symmetric coefficient transfer, Toeplitz determinant, dual
Jacobi–Trudi identity, and positive tableau-tail restriction. Current
`CosineProduct.lean` proves only multipliability and two series evaluations;
it does not yet identify the product with the frozen factorial series. The
Schur/tableau and normalized-existence steps are also unproved in Lean.

The finite theorem for `1≤m≤15`, reduction, and universal-pair transport
already exist in separate reviewed modules. This conditional lemma alone
cannot inhabit `NLA.Statements.MF03.Target`; it must never be labeled as a
full-target proof. Neither the canonical problem ID/path nor any frozen
statement, existing proof module, inventory, or CI file changes here. No
Lean implementation of this contract begins before independent review.

## Source binding

SHA-256 at contract time:

| Source | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| `references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56cfb5abf542a18ff36247b` |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `docs/lean/proofs/MF-03/ALL_ORDER_SOURCE_OBLIGATIONS.md` | `96399593ee86dedb1020da3f9d9301e865c82eec1c801917edcf587e59a58aa6` |
| `lean-statements/NLA/Proofs/MF03/Disk.lean` | `c7ced478264defa6a8365df21c2cb3d861adc18c37d67c793c3336df14d7f53a` |
| `lean-statements/NLA/Proofs/MF03/CosineTail.lean` | `41fc5b7da2f1033b17608a56507aeeba555099f933a1b5eea05477331e8ace8b` |
| `lean-statements/NLA/Proofs/MF03/WaveAtThree.lean` | `824320b42ef6c052c12f6e68ebfb774a4ed969544a70f32a47cd0d8102682b6a` |
| `lean-statements/NLA/Proofs/MF03/CosineProduct.lean` | `a80cd280636110b108e0a13702a55c57d15b739cfc1e73f73bd76eb330689c8a` |
| `lean-statements/NLA/Proofs/MF03/Reduction.lean` | `0e58cdba5a4302aa025201e73143a4c3056f33fc43c618da6bf4aa0095da89cb` |
| `lean-statements/NLA/Proofs/MF03/Transport.lean` | `902e6c7caf52f462d2bc11fcdf713306f69d67d8da0a159b01713ae31fc6cb66` |
| `lean-statements/NLA/Proofs/MF03/FiniteRange.lean` | `b83eadb2aa7bb33dfaf8f553be0ae16df5cab60762a90ff11cea2e609f38278a` |

The mathematical source is manuscript Lemma 2's coefficient estimate,
Lemma 3's disk budget, and the `m≥16` paragraph following its proof.
