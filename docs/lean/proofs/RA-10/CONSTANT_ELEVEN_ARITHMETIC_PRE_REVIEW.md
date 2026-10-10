# RA-10 exact constant-eleven arithmetic gate

**Status:** source-locked mathematical and numerical precontract for independent review. It is an internal conditional composition lemma, not a proof of `TransferBound 11` or `Target`.

## Source lock

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `docs/lean/proofs/RA-10/CONSTANT_ELEVEN_TRANSFER_PRE_REVIEW.md` | `43ec3208c3177ff931289bc236f9afa32796c25be96fc07127027654f2623a92` |

The solution's Equations (15)–(21) use `g=1/(s+c)>0`, `e=e(B)=‖A−B‖_*−τ`, `e₀=‖A−B₀‖_*−τ`, `r=∑_{i<k}|aᵢ−bᵢ|`, `τ=∑_{i≥k}aᵢ`, `τₛ=∑_{i≥k}aᵢ/(s+aᵢ)`, and `F=‖fₛ(A)−fₛ(B)‖_*`. This gate proves only the exact real-number consequences of the source's remaining matrix premises. The matrix inequalities, identity of these scalars with the frozen norm/truncations, and positive-integral representation remain independent proof obligations. Their absence must remain visible; no assumption is added to the frozen final `Target`.

## Exact mathematical and numerical implications

First, for real `g,e,e₀,r,F,τₛ`, assume

```text
0 ≤ g,
r ≤ e,                                  (16)
e₀ ≤ e+r,                                (17)
F−τₛ ≤ 5g e₀ + g r.                    (15)+(18)
```

Then prove exactly

```text
F−τₛ ≤ 11g e.                          (19)
```

Indeed `5e₀+r ≤5(e+r)+r=5e+6r≤11e`; multiplication by `g≥0` preserves order. The number `11` is literal and is neither rounded nor a placeholder. The proof does not divide by `e`, `τ`, or `g`, so it includes `e=0` and `g=0` internally. The full positive-tail branch later has `g>0`; permitting zero in this arithmetic lemma is harmless and does not weaken the target.

Second, for real `F,τₛ,g,e,ε,τ`, assume

```text
0 ≤ g, 0 ≤ ε,
F−τₛ ≤ 11g e,                         (19)
e ≤ ετ,                                 frozen premise after subtracting τ
gτ ≤ τₛ.                                (20)
```

Then prove exactly

```text
F ≤ (1+11ε)τₛ.                         (21)
```

Multiplying `e≤ετ` by `11g≥0`, then `gτ≤τₛ` by `11ε≥0`, yields this result without division or loss in the coefficient. The full proof must separately establish nonnegative `τ`, `τₛ`, and the frozen premise's conversion to `e≤ετ`; they are known from PSD eigenvalues and the exact norm/optimal-tail bridge. The second arithmetic implication itself does not need these as extra assumptions.

## Proposed exact Lean declarations

Implement in a separate `NLA.Proofs.RA10.ConstantElevenArithmetic` module, importing the frozen RA-10 statement and standard Mathlib:

```lean
namespace NLA.Proofs.RA10

theorem ridgeExcess_le_eleven
    {g e e₀ r F τs : ℝ}
    (hg : 0 ≤ g) (hr : r ≤ e) (he₀ : e₀ ≤ e + r)
    (hfive : F - τs ≤ 5 * g * e₀ + g * r) :
    F - τs ≤ 11 * g * e := by
  ...

theorem ridgeTransfer_of_excess
    {F τs g e ε τ : ℝ}
    (hg : 0 ≤ g) (hε : 0 ≤ ε)
    (hexcess : F - τs ≤ 11 * g * e)
    (he : e ≤ ε * τ) (htail : g * τ ≤ τs) :
    F ≤ (1 + 11 * ε) * τs := by
  ...

end NLA.Proofs.RA10
```

The assumptions retain the exact source direction and all coefficients; they are conditional *internal* facts only. No matrix is assumed to commute, no basis is selected, and no theorem is claimed about the frozen `TransferBound` from these scalar premises alone.

## Review and verification

Independent pre-review must check the source quantities, the `5+6=11` chain, signs needed to multiply each inequality, zero cases, and the exact correspondence to (19)/(21) before coding. Then direct pinned Lean 4.33.1/LeanCert kernel build, frozen-source imported exact-signature/axiom audit, and aggregate import. Report the gate as partial until all matrix and operator-monotone dependencies are kernel-proved.
