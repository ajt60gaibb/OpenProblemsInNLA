import Mathlib
import LeanCert.Tactic.Verification

/-! Finite internal half-nets with dimension-sharp cardinality.
The exact contract was independently approved before implementation. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Set Metric Module
namespace NLA.IE06.FiniteNet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem half_separated_card (T : Finset E) (hT : ∀ x ∈ T, ‖x‖ ≤ 1)
    (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → (1:ℝ)/2 ≤ dist x y) :
    T.card ≤ 5^finrank ℝ E := by
  classical
  let f : E → E := fun x => (2:ℝ) • x
  have hinj : Function.Injective f := (smul_right_injective E (by norm_num : (2:ℝ)≠0))
  have hc := Besicovitch.card_le_of_separated (T.image f) ?_ ?_
  · simpa only [Finset.card_image_of_injective T hinj] using hc
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    dsimp [f]
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)]
    linarith [hT x hx]
  · intro z hz w hw hzw
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hw
    have hxy : x≠y := fun h => hzw (congrArg f h)
    have hh := hsep x hx y hy hxy
    dsimp [f]
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)]
    rw [dist_eq_norm] at hh
    linarith

theorem exists_half_net (S : Set E) (hS : ∀ x ∈ S, ‖x‖ ≤ 1) :
    ∃ T : Finset E, (↑T : Set E) ⊆ S ∧ T.card ≤ 5^finrank ℝ E ∧
      ∀ x ∈ S, ∃ y ∈ T, dist x y ≤ (1:ℝ)/2 := by
  classical
  let P : ℕ → Prop := fun k => ∃ T : Finset E, T.card=k ∧ (↑T : Set E)⊆S ∧
    ∀ x ∈ T, ∀ y ∈ T, x≠y → (1:ℝ)/2 ≤ dist x y
  have hzero : P 0 := ⟨∅,by simp,by simp,by simp⟩
  have hmax := Nat.findGreatest_spec (Nat.zero_le (5^finrank ℝ E)) hzero
  obtain ⟨T,hcard,hsub,hsep⟩ := hmax
  have hbound : T.card ≤ 5^finrank ℝ E :=
    half_separated_card T (fun x hx => hS x (hsub hx)) hsep
  refine ⟨T,hsub,hbound,?_⟩
  intro x hx
  by_contra! hfar
  have hnot : x∉T := by
    intro h
    have hh := hfar x h
    norm_num at hh
  have hsub' : (↑(insert x T) : Set E)⊆S := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hyT
    · exact hx
    · exact hsub hyT
  have hsep' : ∀ y ∈ insert x T, ∀ z ∈ insert x T, y≠z → (1:ℝ)/2 ≤ dist y z := by
    intro y hy z hz hyz
    rcases Finset.mem_insert.mp hy with rfl | hyT
    · rcases Finset.mem_insert.mp hz with rfl | hz
      · exact False.elim (hyz rfl)
      · exact (hfar z hz).le
    · rcases Finset.mem_insert.mp hz with rfl | hz
      · rw [dist_comm]
        exact (hfar y hyT).le
      · exact hsep y hyT z hz hyz
  have hbound' : (insert x T).card ≤ 5^finrank ℝ E :=
    half_separated_card _ (fun y hy => hS y (hsub' hy)) hsep'
  have hP : P (insert x T).card := ⟨insert x T,rfl,hsub',hsep'⟩
  have hh := Nat.le_findGreatest hbound' hP
  rw [← hcard, Finset.card_insert_of_notMem hnot] at hh
  omega

omit [FiniteDimensional ℝ E] in
theorem opNorm_le_twice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (T : Finset E)
    (hcover : ∀ x : E, ‖x‖=1 → ∃ y∈T, dist x y ≤ (1:ℝ)/2)
    {B : ℝ} (hB : 0 ≤ B) (hT : ∀ y∈T, ‖A y‖ ≤ B) : ‖A‖ ≤ 2*B := by
  have h : ‖A‖ ≤ B+‖A‖/2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    obtain ⟨y,hy,hxy⟩ := hcover x hx
    have hd : ‖x-y‖ ≤ (1:ℝ)/2 := by simpa only [dist_eq_norm] using hxy
    calc
      ‖A x‖ = ‖A (x-y)+A y‖ := by rw [map_sub, sub_add_cancel]
      _ ≤ ‖A (x-y)‖+‖A y‖ := norm_add_le _ _
      _ ≤ ‖A‖*‖x-y‖+B := add_le_add (A.le_opNorm _) (hT y hy)
      _ ≤ B+‖A‖/2 := by nlinarith [norm_nonneg A]
  linarith

#assert_trust kernel half_separated_card
#assert_trust kernel exists_half_net
#assert_trust kernel opNorm_le_twice
#print axioms half_separated_card
#print axioms exists_half_net
#print axioms opNorm_le_twice

end NLA.IE06.FiniteNet
