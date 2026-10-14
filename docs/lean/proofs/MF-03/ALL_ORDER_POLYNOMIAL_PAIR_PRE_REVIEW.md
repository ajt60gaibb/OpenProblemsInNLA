# MF-03 exact all-order normalized polynomial pair

**Status:** source-locked mathematical, coefficient-indexing, and numerical
precontract for independent review before implementing the polynomial pair.
The original frozen `NormalizedPadeRepresentation` and full `Target` must
remain unchanged. This gate constructs a genuine witness from the already
kernel-proved original determinant coefficients, without per-order solving.

## Denominator and numerator

Fix any `m:ℕ` (including zero). Let the original real nonconstant
coefficient vector be `q_c=cosinePadeNonconstantCoeff m c`, `c:Fin m`.
Its index `c` corresponds to the coefficient of degree `c.val+1`.
Construct the complex polynomial **exactly** as

```text
Q_m = C(1) + Σ c:Fin m, C((q_c:ℂ)) * X^(c.val+1).
```

Hence `Q_m.coeff 0=1`, `Q_m.coeff(c.val+1)=(q_c:ℂ)` for all `c:Fin m`,
`Q_m.coeff j=0` for `j>m`, and `Q_m.natDegree≤m`. The coefficient
exponents `1,…,m` are distinct; no `q₀` is read from the Cramer vector.
At `m=0`, the sum is empty and `Q_0=1`.

For every `n≤m`, let

```text
a_n = Σ i∈range(n+1), Q_m.coeff i /
        (((2*(n-i)).factorial):ℂ).
P_m = Σ n∈range(m+1), C(a_n) * X^n.
```

Thus `P_m.coeff n=a_n` for `n≤m`, `P_m.coeff n=0` for `n>m`,
`P_m.natDegree≤m`, and at `m=0`, `P_0=1`. These are the **literal**
factorial coefficients in the frozen Padé convolution. The already proved
`cosineElementaryCoeff_eq_factorial` identifies them with the original
elementary-symmetric `e_n`; complex coercion introduces no extra factor.

## High-degree equations

For `n=m+r.val+1`, `r:Fin m`, we have `m+1≤n≤2m`. Terms in the frozen
convolution with `i>m` vanish by the degree bound. The `i=0` term is
`e_(m+r.val+1)`. Reindex the remaining `i=1,…,m` by `c:Fin m` with
`i=c.val+1`. Their exact coefficients are

```text
q_c * e_(m+r.val-c.val) = q_c * T(r,c).
```

This is precisely row `r` of the kernel-proved exact system
`T *ᵥ q = b`, whose RHS is `−e_(m+r.val+1)`. Therefore the full
convolution is zero, agreeing with `P_m.coeff n=0`. No row, endpoint,
or factor is skipped: `r=m−1` gives degree `2m` exactly. Together
with the low-degree construction, this proves the actual frozen
`NormalizedPadeRepresentation m P_m Q_m` for **every** `m`.

## Coefficient bound for the large-order disk gate

For every `j` with `1≤j≤m`, set `c=j−1:Fin m`. Real-to-complex norm
preserves absolute value, so the independently reviewed exact
coefficient-one bound gives

```text
‖Q_m.coeff j‖ = |q_c| ≤ (cosineTail m)^j.
```

This is exactly the premise of the existing kernel-proved
`largeOrder_disk_of_tail_coefficients` for `m≥16`, with no changed
threshold, radius `3`, or error `2`. The polynomial pair itself need
not be reduced; the separately kernel-proved reduction/transport gates
will handle all reduced representatives after the normalized witness
and coefficient bound are proved. This precontract does not claim the
full Target until those gates are applied.

## Proposed audited stages

1. Denominator construction and exact coefficient/degree lemmas, with
   a separate imported audit.
2. Numerator construction and exact coefficient/degree lemmas, with
   a separate imported audit.
3. Every frozen normalized Padé equation, including degree `2m`, and
   the complex norm tail bound, with a separate imported audit.
4. Apply existing large-order disk, reduction, and transport to the
   original all-order Target, alongside the already proved orders
   `1,…,15`. Do not assert this final result before each dependency is
   kernel proved.

## Source locks

| Source | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| `references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56cfb5abf542a18ff36247b` |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `lean-statements/NLA/Proofs/MF03/PadeNonconstantCoefficients.lean` | `10149304072ac0bce64065282058b3483b4c60290a2270a495b7c817bad66b77` |
| `lean-statements/NLA/Proofs/MF03/CosineCoefficientTransfer.lean` | `b17175f8a9ed18507e98beffe08cb7d02fb802380437155aafb518c0dc05da60` |
| `lean-statements/NLA/Proofs/MF03/LargeOrderDisk.lean` | `0bd595d22ae9237d608cfe9bf1e521e3ca5869df83ea729e8862e98ef493c7ec` |
| `lean-statements/NLA/Proofs/MF03/Reduction.lean` | `0e58cdba5a4302aa025201e73143a4c3056f33fc43c618da6bf4aa0095da89cb` |

Independent review must check exact source IDs and coefficients,
`Fin m`/one-based degree correspondence, high-system row/column
orientation, all zero and endpoint cases, preservation of complex
absolute value, and the unchanged constants `16`, `3`, `2`, and
coefficient one. After approval, implement symbolic all-order lemmas
under pinned LeanCert kernel trust, with no `sorry`, new axiom,
`native_decide`, unsafe declaration, or finite-order enumeration.
