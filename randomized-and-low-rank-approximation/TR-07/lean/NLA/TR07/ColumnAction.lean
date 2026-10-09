import NLA.TR07.Definitions
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Column synthesis and coordinate restrictions

These internal definitions work with arbitrary finite column labels. All
coefficient norms use the Euclidean space, including intermediate restrictions.
-/

noncomputable section
open scoped BigOperators

namespace NLA.TR07

variable {ι κ E : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Synthesis by an indexed family of columns. -/
def synthesis (a : ι → E) : EuclideanSpace ℝ ι →ₗ[ℝ] E where
  toFun x := ∑ i, x i • a i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_smul]

@[simp] theorem synthesis_apply (a : ι → E) (x : EuclideanSpace ℝ ι) :
    synthesis a x = ∑ i, x i • a i := rfl

/-- A lower bound on all coefficient vectors supported in the indicated set. -/
def Good (a : ι → E) (η : ℝ) (S : Finset ι) : Prop :=
  ∀ x : EuclideanSpace ℝ ι, (∀ i, i ∉ S → x i = 0) →
    η * ‖x‖ ≤ ‖synthesis a x‖

theorem good_empty (a : ι → E) (η : ℝ) : Good a η ∅ := by
  intro x hx
  have : x = 0 := by ext i; exact hx i (Finset.notMem_empty i)
  simp [this]

theorem Good.mono {a : ι → E} {η : ℝ} {S T : Finset ι}
    (h : Good a η S) (hTS : T ⊆ S) : Good a η T := by
  intro x hx
  exact h x fun i hi => hx i fun hit => hi (hTS hit)

theorem Good.congr {a b : ι → E} {η : ℝ} {S : Finset ι}
    (h : Good a η S) (hab : ∀ i ∈ S, a i = b i) : Good b η S := by
  intro x hx
  have he : synthesis a x = synthesis b x := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ S
    · rw [hab i hi]
    · simp [hx i hi]
  rw [← he]
  exact h x hx

/-- Transport coefficients along a bijection of their finite labels. -/
def reindex (e : ι ≃ κ) : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e

@[simp] theorem reindex_apply (e : ι ≃ κ) (x : EuclideanSpace ℝ ι) (j : κ) :
    reindex e x j = x (e.symm j) := rfl

theorem synthesis_reindex (e : ι ≃ κ) (a : κ → E) (x : EuclideanSpace ℝ ι) :
    synthesis a (reindex e x) = synthesis (a ∘ e) x := by
  classical
  exact Fintype.sum_equiv e.symm _ _ fun j => by simp

theorem Good.reindex (e : ι ≃ κ) {a : κ → E} {η : ℝ} {S : Finset κ}
    (h : Good a η S) : Good (a ∘ e) η (S.preimage e e.injective.injOn) := by
  classical
  intro x hx
  have he := h (NLA.TR07.reindex e x) (by
    intro j hj
    apply hx
    simpa using hj)
  rw [synthesis_reindex] at he
  simpa only [LinearIsometryEquiv.norm_map] using he

theorem norm_normalize {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℝ ι) (hx : x ≠ 0) : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
  exact norm_smul_inv_norm hx

theorem selectedAction_eq_synthesis {k n : ℕ} (M : Mat k n) (I : Finset (Fin n))
    (x : EuclideanSpace ℝ I) :
    selectedAction M I x = synthesis (fun j : I => WithLp.toLp 2 (fun i => M i j)) x := by
  ext i
  simp [selectedAction, synthesis, mul_comm]

theorem selected_unit_le {k n : ℕ} (M : Mat k n) (I : Finset (Fin n))
    (x : EuclideanSpace ℝ I) (hx : ‖x‖ = 1) :
    smallestSingular M I ≤ ‖selectedAction M I x‖ := by
  apply csInf_le
  · exact ⟨0, fun y hy => by obtain ⟨x, _, rfl⟩ := hy; exact norm_nonneg _⟩
  · exact ⟨x, hx, rfl⟩

theorem good_selected_of_tail {k n : ℕ} (M : Mat k n) (I : Finset (Fin n))
    {η : ℝ} (h : η < smallestSingular M I) :
    Good (fun j : I => WithLp.toLp 2 (fun i => M i j)) η Finset.univ := by
  intro x _
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu := selected_unit_le M I ((‖x‖⁻¹ : ℝ) • x) (norm_normalize x hx)
  rw [selectedAction_eq_synthesis, map_smul, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hn.le)] at hu
  have hh := mul_le_mul_of_nonneg_right (le_trans h.le hu) hn.le
  calc
    η * ‖x‖ ≤ (‖x‖⁻¹ * ‖synthesis (fun j : I => WithLp.toLp 2 (fun i => M i j)) x‖) * ‖x‖ := hh
    _ = _ := by field_simp

end NLA.TR07
