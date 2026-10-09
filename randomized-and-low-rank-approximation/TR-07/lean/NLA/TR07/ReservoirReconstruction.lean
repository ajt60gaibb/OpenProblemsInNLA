import NLA.TR07.ReservoirStep
import NLA.TR07.IdealReconstruction
import NLA.TR07.Reconstructible

/-! Reconstruction from disjoint blocks of actual independent columns. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace NLA.TR07
open Law
variable {α : Type*} [Fintype α] {k s ℓ : ℕ}

omit [Fintype α] in
/-- Every linear combination used by the estimator belongs to the retained reservoir span. -/
theorem reconstruction_mem_span (u : α → Vec k) (L b : ℕ)
    (z : Fin b → Fin L → Fin ℓ → α) (states : Fin b → Fin L → SignedState α)
    (h : ∀ i j, stateVector u (states i j) ∈
      Submodule.span ℝ (Set.range (fun t => u (z i j t)))) :
    reconstruction u L b states ∈ Submodule.span ℝ
      (Set.range (fun t : Fin b × Fin L × Fin ℓ => u (z t.1 t.2.1 t.2.2))) := by
  let V := Submodule.span ℝ
    (Set.range (fun t : Fin b × Fin L × Fin ℓ => u (z t.1 t.2.1 t.2.2)))
  have hh (i : Fin b) (j : Fin L) : stateVector u (states i j) ∈ V := by
    apply (Submodule.span_mono ?_) (h i j)
    rintro _ ⟨t, rfl⟩
    exact ⟨(i,j,t),rfl⟩
  unfold reconstruction average trajectoryEstimator
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (hh i j)

set_option maxHeartbeats 800000 in
/-- The real path law dominates the ideal path law, and every successful
coupled realization supplies an explicit vector in the sampled-column span. -/
theorem reservoir_success_probability (p : Law α) (u : α → Vec k)
    (hu : ∀ a, SignedVector s (u a)) (hk : 0 < k) (hs : 0 < s) (hℓk : ℓ ≤ k)
    (L b : ℕ) (hb : 0 < b) {ε : ℝ} (hε : 0 < ε)
    (hbudget : 2*(s:ℝ)^2/(2*L+1) + (s:ℝ)*((2:ℝ)^L-1)^2/b ≤ ε^2/4)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1/2) (hck : c ≤ (ℓ : ℝ)/(2*k)) :
    (3:ℝ)/4 * c^(L*b) ≤
      p.expect (fun a => (((p.iid ℓ).iid L).iid b).prob (fun z =>
        Reconstructible (u a)
          (fun t : Fin b × Fin L × Fin ℓ => u (z t.1 t.2.1 t.2.2)) ε)) := by
  let K := idealKernel p u hu hk hs
  let H := reservoirKernel p u hu hs ℓ
  let Q (a : α) := coupledPaths (p.iid ℓ) (reservoirStep u hu hs) L (some (false,a))
  have hstates (a : α) : (Q a).map Prod.snd = paths H L (some (false,a)) := by
    apply (expect_eq_iff _ _).mp
    intro f
    rw [expect_map]
    exact coupledPaths_states _ _ _ _ f
  have hinputs (a : α) : (Q a).map Prod.fst = (p.iid ℓ).iid L := by
    apply (expect_eq_iff _ _).mp
    intro f
    rw [expect_map]
    exact coupledPaths_inputs _ _ _ _ f
  have hdom (a : α) (z : Fin L → SignedState α) :
      c^L * (paths K L (some (false,a))).wt z ≤ (paths H L (some (false,a))).wt z := by
    rw [wt_eq_expect, wt_eq_expect]
    exact paths_scaled_expect_le K H hc0
      (reservoirKernel_dominates p u hu hk hs hℓk hc0 hc1 hck) L _ _
      (fun _ => by split_ifs <;> norm_num)
  have hone (a : α) :
      c^(L*b) * ((paths K L (some (false,a))).iid b).prob
        (fun z => ‖u a - reconstruction u L b z‖ ≤ ε) ≤
      (((p.iid ℓ).iid L).iid b).prob (fun z => Reconstructible (u a)
        (fun t : Fin b × Fin L × Fin ℓ => u (z t.1 t.2.1 t.2.2)) ε) := by
    have hmass := iid_scaled _ _ (pow_nonneg hc0 L) (hdom a) b
    have hscaled := scaled_expect_le _ _ hmass
      (fun z => @ite ℝ (‖u a - reconstruction u L b z‖ ≤ ε) (Classical.propDecidable _) 1 0)
      (fun _ => by split_ifs <;> norm_num)
    rw [← pow_mul] at hscaled
    change c^(L*b) * _ ≤ _ at hscaled
    apply hscaled.trans
    rw [← hstates a]
    unfold prob
    rw [iid_map_expect, ← hinputs a, iid_map_expect]
    apply expect_mono_on_support
    intro out hout
    have hspan : reconstruction u L b (fun i => (out i).2) ∈
        Submodule.span ℝ (Set.range
          (fun t : Fin b × Fin L × Fin ℓ => u ((out t.1).1 t.2.1 t.2.2))) := by
      apply reconstruction_mem_span u L b (fun i => (out i).1) (fun i => (out i).2)
      intro i j
      exact coupledPaths_local_support (p.iid ℓ) (reservoirStep u hu hs)
        (fun z y => stateVector u y ∈ Submodule.span ℝ (Set.range (fun t => u (z t))))
        (reservoirStep_span u hu hs) L _ (out i) (iid_pos_coordinate _ out hout i) j
    by_cases he : ‖u a - reconstruction u L b (fun i => (out i).2)‖ ≤ ε
    · have hr : Reconstructible (u a)
          (fun t : Fin b × Fin L × Fin ℓ => u ((out t.1).1 t.2.1 t.2.2)) ε :=
        ⟨_, hspan, he⟩
      simp only [if_pos he, if_pos hr, le_refl]
    · simp only [if_neg he]
      split_ifs <;> norm_num
  have hsuccess := ideal_success_probability p u hu hk hs L b hb hε hbudget
  unfold idealExperiment prob at hsuccess
  simp only [expect_bind, expect_map] at hsuccess
  have hsuccess' : (3:ℝ)/4 ≤ p.expect
      (fun a => ((paths K L (some (false,a))).iid b).prob
        (fun z => ‖u a - reconstruction u L b z‖ ≤ ε)) := by
    convert hsuccess using 1
    apply p.expect_congr
    intro a
    unfold prob
    apply expect_congr
    intro z
    split_ifs <;> rfl
  calc
    (3:ℝ)/4 * c^(L*b) ≤ c^(L*b) * p.expect
        (fun a => ((paths K L (some (false,a))).iid b).prob
          (fun z => ‖u a - reconstruction u L b z‖ ≤ ε)) := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsuccess' (pow_nonneg hc0 (L*b))
    _ = p.expect (fun a => c^(L*b) * ((paths K L (some (false,a))).iid b).prob
        (fun z => ‖u a - reconstruction u L b z‖ ≤ ε)) := (expect_const_mul _ _ _).symm
    _ ≤ _ := p.expect_mono hone

end NLA.TR07
