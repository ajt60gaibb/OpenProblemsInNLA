import NLA.Proofs.TR14.MomentIndex
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
The exact finite apolar convolution and its least nonzero kernel degree for
nonzero moment vectors. A coefficient vector here is a homogeneous form of
its stated degree; no affine leading coefficient is assumed nonzero.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.TR14

/-- The degree-`d` apolar map has one equation for every shift through
`D - d`, with no truncated or defaulted moment indices. -/
noncomputable def apolarMap {D : ℕ} (h : Fin (D + 1) → ℂ)
    (d : ℕ) (hd : d ≤ D) :
    (Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin (D - d + 1) → ℂ) where
  toFun g j := ∑ i : Fin (d + 1), g i * h ⟨i.val + j.val, by
    have hi := i.isLt
    have hj := j.isLt
    omega⟩
  map_add' := by
    intro g f
    funext j
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c g
    funext j
    simp [Finset.mul_sum, mul_assoc]

/-- The homogeneous coefficient vector belongs to the exact apolar kernel. -/
def IsApolar {D : ℕ} (h : Fin (D + 1) → ℂ)
    (d : ℕ) (hd : d ≤ D) (g : Fin (d + 1) → ℂ) : Prop :=
  apolarMap h d hd g = 0

/-- At homogeneous degree zero, apolarity says that the constant coefficient
annihilates every moment. -/
theorem apolar_zero_degree_iff {D : ℕ} (h : Fin (D + 1) → ℂ)
    (g : Fin 1 → ℂ) :
    IsApolar h 0 (Nat.zero_le D) g ↔
      ∀ j : Fin (D + 1), g 0 * h j = 0 := by
  simp [IsApolar, apolarMap, funext_iff]

/-- A nonzero moment vector has no nonzero degree-zero apolar form. -/
theorem apolar_zero_degree_eq_zero {D : ℕ} (h : Fin (D + 1) → ℂ)
    (hh : h ≠ 0) (g : Fin 1 → ℂ)
    (hg : IsApolar h 0 (Nat.zero_le D) g) : g = 0 := by
  obtain ⟨j, hj⟩ : ∃ j : Fin (D + 1), h j ≠ 0 := by
    by_contra hx
    simp only [not_exists, not_not] at hx
    apply hh
    funext j
    exact hx j
  have hgj := (apolar_zero_degree_iff h g).mp hg j
  have hg0 : g 0 = 0 := (mul_eq_zero.mp hgj).resolve_right hj
  funext i
  fin_cases i
  exact hg0

/-- In every positive moment length, the first degree above half has more
coefficient variables than apolar equations. -/
theorem apolar_mid_kernel_nontrivial {D : ℕ} (h : Fin (D + 1) → ℂ)
    (hD : 1 ≤ D) :
    ∃ g : Fin (D / 2 + 2) → ℂ,
      g ≠ 0 ∧ IsApolar h (D / 2 + 1) (by omega) g := by
  have hd : D / 2 + 1 ≤ D := by omega
  have hdim : Module.finrank ℂ (Fin (D - (D / 2 + 1) + 1) → ℂ) <
      Module.finrank ℂ (Fin (D / 2 + 2) → ℂ) := by
    simp [Module.finrank_fintype_fun_eq_card]
    omega
  have hker : LinearMap.ker (apolarMap h (D / 2 + 1) hd) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨g, hgker, hg0⟩ :=
    (LinearMap.ker (apolarMap h (D / 2 + 1) hd)).ne_bot_iff.mp hker
  refine ⟨g, hg0, ?_⟩
  exact (LinearMap.mem_ker.mp hgker)

/-- The least nonzero apolar degree, with all smaller homogeneous kernels
trivial. The index is distinct from a target decomposition width. -/
theorem minimal_apolar_exists {D : ℕ} (h : Fin (D + 1) → ℂ)
    (hD : 1 ≤ D) (hh : h ≠ 0) :
    ∃ r₀ : ℕ, ∃ hrD : r₀ ≤ D,
      1 ≤ r₀ ∧ r₀ ≤ D / 2 + 1 ∧
      (∃ g : Fin (r₀ + 1) → ℂ,
        g ≠ 0 ∧ IsApolar h r₀ hrD g) ∧
      (∀ d : ℕ, ∀ hd : d ≤ D, d < r₀ →
        ∀ b : Fin (d + 1) → ℂ, IsApolar h d hd b → b = 0) := by
  classical
  let P : ℕ → Prop := fun d =>
    ∃ hd : d ≤ D, ∃ g : Fin (d + 1) → ℂ,
      g ≠ 0 ∧ IsApolar h d hd g
  have hP : ∃ d, P d := by
    obtain ⟨g, hg0, hg⟩ := apolar_mid_kernel_nontrivial h hD
    exact ⟨D / 2 + 1, by omega, g, hg0, hg⟩
  let r₀ := Nat.find hP
  obtain ⟨hrD, g, hg0, hg⟩ := Nat.find_spec hP
  have hrHi : r₀ ≤ D / 2 + 1 :=
    Nat.find_min' hP (by
      obtain ⟨g', hg'0, hg'⟩ := apolar_mid_kernel_nontrivial h hD
      exact ⟨by omega, g', hg'0, hg'⟩)
  have hrLo : 1 ≤ r₀ := by
    by_contra hx
    have hrZero : r₀ = 0 := by omega
    have hspec : P r₀ := Nat.find_spec hP
    have hzero : P 0 := hrZero ▸ hspec
    obtain ⟨_, g₀, hg₀, hgap⟩ := hzero
    exact hg₀ (apolar_zero_degree_eq_zero h hh g₀ hgap)
  refine ⟨r₀, hrD, hrLo, hrHi, ⟨g, hg0, hg⟩, ?_⟩
  intro d hd hlt b hb
  by_contra hb0
  exact (Nat.find_min hP hlt) ⟨hd, b, hb0, hb⟩

/-- The middle-degree bound leaves only the balanced or unbalanced
numerical cases used in the quotient argument. -/
theorem minimal_apolar_balanced_or_unbalanced {D r₀ : ℕ}
    (hrLo : 1 ≤ r₀) (hrHi : r₀ ≤ D / 2 + 1) :
    D = 2 * r₀ - 2 ∨ 2 * r₀ - 1 ≤ D := by
  omega

#assert_trust kernel apolarMap
#assert_trust kernel apolar_zero_degree_iff
#assert_trust kernel apolar_zero_degree_eq_zero
#assert_trust kernel apolar_mid_kernel_nontrivial
#assert_trust kernel minimal_apolar_exists
#assert_trust kernel minimal_apolar_balanced_or_unbalanced
#print axioms minimal_apolar_exists

end NLA.Proofs.TR14
