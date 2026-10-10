# RA-10 pinching reflection algebra: exact staged precontract

**Status:** mathematical and exact-signature precontract for independent review; no Lean implementation or nuclear contraction is claimed.

## Source lock and relation to the approved gate

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `docs/lean/proofs/RA-10/NUCLEAR_PINCHING_GATE_PRE_REVIEW.md` | `23d850db3f312e04a30d732e1e9f030f04b80f5c7eff1584c4711a3aa435ffa1` |

The approved nuclear pinching gate requires proving that the frozen nuclear norm is contractive under two-block pinching, as used in source Equation (8). This staged theorem package proves the exact **matrix algebra** underneath that contraction. It does not prove the frozen nuclear triangle inequality, singular-value invariance, homogeneity, or the coefficient-`1` norm bound. Those remain open until separately kernel-proved. No original RA-10 statement, ID, selected basis, or final quantifier changes.

## Exact mathematics and boundaries

For every `n : ℕ` and real square `P,M`, define the reflection `U=P+P−I`, which is exactly `2P−I`, and the pinching `Pinch_P(M)=PMP+(I−P)M(I−P)` with the matrix multiplication order shown. If `Pᵀ=P`, then `Uᵀ=U`. If `P²=P`, then `U²=I`, since `(2P−I)²=4P²−4P+I`. Together these imply `UᵀU=UUᵀ=I`: the reflection is orthogonal even when `P` has rank `0` or `n`.

For **all** `P,M`, without a symmetry or idempotence assumption, prove the exact algebraic identity

```text
Pinch_P(M) = (1/2) • (M + U M U).
```

Indeed `M+UMU=2M−2PM−2MP+4PMP` and `2 Pinch_P(M)=2M−2PM−2MP+4PMP`. The real scalar factor is literally `1/2`, with no numerical approximation. This includes `n=0` and arbitrary nonsymmetric `M`. The source's selected projection must eventually be shown symmetric/idempotent from its supplied orthonormal columns, not assumed in the frozen `Target`.

## Proposed exact Lean declarations

Use a separate `NLA.Proofs.RA10.PinchingReflection` module. Matrix types may be annotated explicitly, but no theorem assumptions or conclusions may change:

```lean
namespace NLA.Proofs.RA10

def reflection {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := P + P - 1

def pinch {n : ℕ} (P M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  P * M * P + (1 - P) * M * (1 - P)

theorem reflection_transpose {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (hsym : P.transpose = P) :
    (reflection P).transpose = reflection P := by
  ...

theorem reflection_square {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (hid : P * P = P) :
    reflection P * reflection P = 1 := by
  ...

theorem reflection_orthogonal {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hsym : P.transpose = P) (hid : P * P = P) :
    (reflection P).transpose * reflection P = 1 ∧
      reflection P * (reflection P).transpose = 1 := by
  ...

theorem pinch_eq_reflection_average {n : ℕ}
    (P M : Matrix (Fin n) (Fin n) ℝ) :
    pinch P M = (1 / 2 : ℝ) • (M + reflection P * M * reflection P) := by
  ...

end NLA.Proofs.RA10
```

For the last theorem, `reflection P * M * reflection P` is left-associated, matching the source's `UMU`. The definition of `pinch` exactly matches the approved coefficient-`1` nuclear gate. The algebraic average alone makes **no** nuclear-norm assertion; that distinction must remain visible in module documentation and inventory.

## Review and verification

Independent pre-review must check noncommutative multiplication order, the `2P−I` expansion, equality at `P=0` and `P=I`, `n=0`, and exact factor `1/2`. Only then implement, direct-build with pinned Lean 4.33.1 in LeanCert kernel mode, freeze source, and independently audit imported exact signatures/axioms before aggregate import. If the norm dependencies stay unproved, report the full pinching contraction as open.
