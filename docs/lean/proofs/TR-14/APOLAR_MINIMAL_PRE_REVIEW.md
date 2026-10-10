# TR-14 apolar map and minimal degree: exact pre-proof contract

**Author:** `/root/ra06_sampling_review` (AI agent), 10 October 2026. **Status:** frozen mathematical/Lean interface proposal for independent review before source implementation. This is the first apolar component of the approved finite moment algebra contract, not a proof of `NLA.Statements.TR14.Target`.

## Frozen mathematical object

For `D=m(n−1)` in the frozen target (`m≥3`, `n≥2`, hence `D≥3`), take `h : Fin(D+1) → ℂ`. For any `d≤D`, let `V_d=Fin(d+1)→ℂ`. A vector `g∈V_d` represents the homogeneous **degree-`d`** form

\[
 G_d(X,Y)=\sum_{i=0}^{d}g_iX^{d-i}Y^i.
\]

Define the exact linear apolar map `C_{h,d}:V_d→Fin(D−d+1)→ℂ` by

\[
 (C_{h,d}g)_j=\sum_{i=0}^{d}g_i h_{i+j},
 \qquad 0\le j\le D-d.
\]

Thus `I_d=ker C_{h,d}` is the source's apolar space, including all endpoint equations `j=0` and `j=D−d`. The matrix has **`D−d+1` rows** and **`d+1` columns**. All `h_{i+j}` have indices `≤D` by these ranges; the implementation must prove that bound, never truncate or default to zero. A trailing zero `g_d` is permitted: it records a root of the homogeneous form at infinity, and excluding it would weaken the all-moment target. The form is zero iff every coefficient is zero. For `d>D`, the source convention is `I_d=V_d`; this first module may stay at `d≤D` because its existence witness is in that range. Any later all-degree API must implement the source convention explicitly.

The source's `I_d` is a homogeneous ideal: for `d<D`, multiplication by `X` extends the coefficient vector with a trailing zero, and multiplication by `Y` shifts it with a leading zero. For `g∈I_d`, both lie in `I_{d+1}` because the new equation range `0≤j≤D−d−1` is a subset of the old range, with the `Y` equation using old index `j+1≤D−d`. If this module exposes these maps, their formulas and ranges must be proved; they are not assumptions in minimality.

## Zero, nonzero, and parity endpoints

For `h=0`, every `C_{h,d}` is zero, so `I₀` contains a nonzero constant. Treat the zero Hankel tensor separately using the already frozen `hankel_eq_zero_iff`; do not construct a nondegenerate moment quotient for it. For `h≠0`, choose `j` with `h_j≠0`. Then `g∈I₀` implies `g_0h_j=0`, so `I₀={0}` and any minimal nonzero apolar degree is at least one.

Set `d_* = ⌊D/2⌋+1`. Under `D≥1`, `d_*≤D` and

\[
 d_*+1>D-d_*+1.
\]

Hence the linear map `C_{h,d_*}` from a complex vector space of dimension `d_*+1` to one of dimension `D−d_*+1` has nonzero kernel, **for every** `h`. The exact parity counts are:

| `D` | `d_*` | source dimension | equation count |
| --- | ---: | ---: | ---: |
| `2k`, `k≥1` | `k+1` | `k+2` | `k` |
| `2k+1`, `k≥0` | `k+1` | `k+2` | `k+1` |

In particular, `D=1` is valid for the general finite lemma; `D=0` is excluded from the `d_*≤D` proof and unnecessary for TR-14. The even-dimensional table only asserts kernel dimension **at least** two at `d_*`; the exact two-dimensional balanced apolar space is a later theorem using the Frobenius quotient, not an assumption here. The `D=2` and `r₀=1` cases remain within the finite lemma, although the frozen target has `D≥3`.

Since `d_*` is a witness, choose the least natural `r₀≤d_*` for which `I_{r₀}` contains a nonzero vector. For `h≠0`, prove the **full package**

\[
 1\le r₀\le\lfloor D/2\rfloor+1,
 \qquad \exists,0\ne g\in I_{r₀},
 \qquad \forall d<r₀,\ I_d=\{0\}.
\]

The `d<r₀` quantifier includes `d=0`, and all such `d` automatically satisfy `d≤D`. No chosen form is required to have a nonzero `Y^{r₀}` coefficient. Additionally prove the arithmetic dichotomy used in the next quotient step: either `D=2r₀−2` (balanced, possible only for even `D`) or `D≥2r₀−1`. There is no `D=2r₀−3` branch. This dichotomy is numerical, with no floating-point computation.

## Proposed Lean declarations

The signatures below are API sketches; the final file may package bound proofs differently, but it must export equivalent assertions with the same mathematical quantifiers. One possible implementation is a `LinearMap` over coefficient functions:

```lean
noncomputable def apolarMap {D : ℕ} (h : Fin (D + 1) → ℂ)
    (d : ℕ) (hd : d ≤ D) :
    (Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin (D - d + 1) → ℂ) :=
  -- at j: ∑ i : Fin(d+1), g i * h ⟨i.val+j.val, range proof⟩

def IsApolar {D : ℕ} (h : Fin (D + 1) → ℂ)
    (d : ℕ) (hd : d ≤ D) (g : Fin (d + 1) → ℂ) : Prop :=
  apolarMap h d hd g = 0

theorem apolar_zero_degree_iff {D : ℕ} (h : Fin (D + 1) → ℂ)
    (g : Fin 1 → ℂ) :
  IsApolar h 0 (Nat.zero_le D) g ↔ ∀ j : Fin (D + 1), g 0 * h j = 0

theorem apolar_mid_kernel_nontrivial {D : ℕ} (h : Fin (D + 1) → ℂ)
    (hD : 1 ≤ D) :
  ∃ g : Fin (D / 2 + 2) → ℂ,
    g ≠ 0 ∧ IsApolar h (D / 2 + 1) (by omega) g

theorem minimal_apolar_exists {D : ℕ} (h : Fin (D + 1) → ℂ)
    (hD : 1 ≤ D) (hh : h ≠ 0) :
  ∃ r₀ : ℕ, ∃ hrD : r₀ ≤ D,
    1 ≤ r₀ ∧ r₀ ≤ D / 2 + 1 ∧
    (∃ g : Fin (r₀ + 1) → ℂ,
      g ≠ 0 ∧ IsApolar h r₀ hrD g) ∧
    (∀ d : ℕ, ∀ hd : d ≤ D, d < r₀ →
      ∀ b : Fin (d + 1) → ℂ, IsApolar h d hd b → b = 0)

theorem minimal_apolar_balanced_or_unbalanced
    (hrLo : 1 ≤ r₀) (hrHi : r₀ ≤ D / 2 + 1) :
  D = 2 * r₀ - 2 ∨ 2 * r₀ - 1 ≤ D
```

The `minimal_apolar_exists` witness is existential and may be nonunique as a polynomial; the least **degree** is unique. Its proof should use finite-dimensional rank-nullity (or a proved equivalent) followed by least-number selection. It must not insert a monic affine polynomial, genericity, a nonzero catalecticant determinant, squarefree support, or a particular width into this first statement. Such a `GL₂` normalization belongs to the later quotient theorem. No `sorry`, custom axiom, `native_decide`, or untrusted certificate may close these claims.

## Relation to the unchanged target and source locks

The target still asks `OrdinaryWidth (Hankel h) r ↔ SymmetricWidth (Hankel h) r` for **all** `m≥3`, `n≥2`, `h`, and `r≥0`. The finite apolar package supplies an invariant for nonzero `h` and leaves the Frobenius quotient, middle-rank identification, symmetric upper bounds, arbitrary ordinary lower bound, and padding untouched. `r₀` is **not** the target width `r`.

| Reviewed input | SHA-256 |
| --- | --- |
| Canonical `tensor-computations/TR-14/README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| Proof `tensor-computations/TR-14/solution.tex` (§2, apolar kernel and moment algebra lemma) | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66c282716c14bc6` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Approved `MOMENT_ALGEBRA_PRE_REVIEW.md` | `2297de29286de55999709753278dcf84c1b4dd67640f4064baa98ba93165a840` |
| Frozen `MomentIndex.lean` | `93932adde8ff14713d19a1c813a0ec2ea09a319cff29af242b5028a51ac39435` |

Independent review of this precise contract is required before Lean source. Once source is frozen, the exact signatures and proof must receive a separate hash-bound imported LeanCert kernel and transitive-axiom audit. No partial result here establishes TR-14 `Target`.
