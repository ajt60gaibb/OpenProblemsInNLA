import NLA.IE22.ProjectionEvent
import NLA.IE22.SupremumSemantics

/-! Deterministic extraction from the exact finite Gaussian certificate.
Intermediate lemmas retain their explicit certificate input; the selected
final bound will be assembled from proved spectral and probability results.
Original mathematical proof: Matthew J. Colbrook.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, with AI-agent assistance. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
namespace NLA.IE22
open NLA.IE21

lemma deletionSingular_sq_le_finiteTrim {m d : ℕ} (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (hd : 1 ≤ d) (B : Mat m d) (x : Space d) (hx : ‖x‖ = 1) :
    deletionSingular θ B^2 ≤ finiteTrim (retainedRows θ m) (fun i => (matrixMap B x i)^2) := by
  obtain ⟨⟨S,hS,hval⟩,_⟩ := finiteTrim_minimum (retainedRows θ m)
    (retainedRows_le θ hθ m) (fun i => (matrixMap B x i)^2)
  have hmin := deletion_minimum θ hθ B hd
  rw [hval,← retainedNorm_sq]
  exact pow_le_pow_left₀ hmin.1 (hmin.2.2 S x hS hx) 2

lemma deletionSingular_sq_le_of_projectionGood (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (B : Mat m d)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) (g : Space d) (hg : g ∈ ProjectionGood θ B δ) :
    deletionSingular θ B^2 ≤ (m : ℝ)/((d : ℝ)*(1-δ))*(gaussianTrim θ+2*δ) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hgap : 0 < 1-δ := sub_pos.mpr hδ.2
  have hgnorm : 0 < ‖g‖^2 := (mul_pos hgap hdpos).trans_le hg.2.1
  have hg0 : g ≠ 0 := by intro h; simp [h] at hgnorm
  have hgnorm0 : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg0
  let y : Fin m → ℝ := fun i => (matrixMap B g i)^2
  have hmean : (∑ i, y i)/(m : ℝ) ≤ 2 := by
    simpa only [projectedEnergy,EuclideanSpace.real_norm_sq_eq,y] using hg.1
  obtain ⟨t,ht,htL,hdual,_⟩ := bounded_trimming_threshold θ hθ m hm y
    (fun i => sq_nonneg _) hmean
  have htrim : finiteTrim (retainedRows θ m) y/(m : ℝ) ≤ gaussianTrim θ+2*δ := by
    rw [hdual]
    exact hg.2.2 t ht htL
  let x : Space d := ‖g‖⁻¹ • g
  have hx : ‖x‖ = 1 := norm_smul_inv_norm hg0
  have hscale : finiteTrim (retainedRows θ m) (fun i => (matrixMap B x i)^2) =
      (‖g‖⁻¹)^2*finiteTrim (retainedRows θ m) y := by
    have heq : (fun i => (matrixMap B x i)^2) = fun i => (‖g‖⁻¹)^2*y i := by
      funext i
      simp [x,y,map_smul,PiLp.smul_apply,smul_eq_mul,mul_pow]
    rw [heq]
    exact finiteTrim_smul_nonneg _ (retainedRows_le θ hθ m) _ (sq_nonneg _) y
  have hmin := deletionSingular_sq_le_finiteTrim θ hθ hd B x hx
  rw [hscale] at hmin
  have hscaled : deletionSingular θ B^2*‖g‖^2 ≤ finiteTrim (retainedRows θ m) y := by
    have h := mul_le_mul_of_nonneg_right hmin hgnorm.le
    have heq : (‖g‖⁻¹)^2*finiteTrim (retainedRows θ m) y*‖g‖^2 =
        finiteTrim (retainedRows θ m) y := by field_simp
    rwa [heq] at h
  have hsum : finiteTrim (retainedRows θ m) y ≤ (m : ℝ)*(gaussianTrim θ+2*δ) := by
    have h := (div_le_iff₀ hmpos).mp htrim
    nlinarith
  have hmin0 : 0 ≤ deletionSingular θ B^2 := sq_nonneg _
  have hlower : deletionSingular θ B^2*((d : ℝ)*(1-δ)) ≤
      (m : ℝ)*(gaussianTrim θ+2*δ) := by
    have h := mul_le_mul_of_nonneg_left hg.2.1 hmin0
    nlinarith
  have hden : 0 < (d : ℝ)*(1-δ) := mul_pos hdpos hgap
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hden).2 hlower

/-- A strict explicit failure budget produces an actual finite-dimensional vector. -/
lemma projectionGood_nonempty_of_probability_bound {m d : ℕ} (θ δ : ℝ) (B : Mat m d)
    (F : ℝ) (hF : F < 1)
    (hprob : (stdGaussian (Space d)).real (ProjectionGood θ B δ)ᶜ ≤ F) :
    (ProjectionGood θ B δ).Nonempty := by
  by_contra hne
  have hempty : ProjectionGood θ B δ = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
  rw [hempty,compl_empty,probReal_univ] at hprob
  linarith

/-- Attainment of the genuine supremum transfers a uniform squared matrix bound. -/
lemma supremum_bound_of_all_matrices (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (C : ℝ)
    (hC : ∀ A : Mat m n, UnitRows A → normalizedDeletion θ A ≤ C) :
    extremalValue θ m n^2 ≤ C ∧ extremalValue θ m n ≤ Real.sqrt C := by
  obtain ⟨A,hA,heq⟩ := (supremum_semantics θ hθ m n hm hn).2.2.1
  have hsq : extremalValue θ m n^2 ≤ C := by
    rw [heq,(normalizedSingular_nonneg_sq θ hθ hn A).2]
    exact hC A hA
  exact ⟨hsq,Real.le_sqrt_of_sq_le hsq⟩

/-- A genuinely smaller singular minimum in the ambient domain inherits the
certificate bound, with the ambient dimension retained in the numerator. -/
lemma normalizedDeletion_le_of_projectionGood (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n d : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (A : Mat m n) (B : Mat m d)
    (hmin : deletionSingular θ A ≤ deletionSingular θ B)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) (g : Space d) (hg : g ∈ ProjectionGood θ B δ) :
    normalizedDeletion θ A ≤ (n : ℝ)/((d : ℝ)*(1-δ))*(gaussianTrim θ+2*δ) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hs : deletionSingular θ A^2 ≤ deletionSingular θ B^2 :=
    pow_le_pow_left₀ (deletion_minimum θ hθ A hn).1 hmin 2
  have hbound := hs.trans (deletionSingular_sq_le_of_projectionGood θ hθ m d hm hd B δ hδ g hg)
  have hratio : 0 ≤ (n : ℝ)/m := div_nonneg (Nat.cast_nonneg n) hmpos.le
  unfold normalizedDeletion
  calc
    _ ≤ (n : ℝ)/m*((m : ℝ)/((d : ℝ)*(1-δ))*(gaussianTrim θ+2*δ)) :=
      mul_le_mul_of_nonneg_left hbound hratio
    _ = _ := by field_simp

/-- Explicit intermediate bridge. The actual spectral and event results must
supply the displayed relation/probability estimate in the selected theorem. -/
lemma deterministic_bound_of_projected_probability (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r ∧ r < n)
    (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) (hfail : deterministicFailure θ n r δ < 1)
    (A : Mat m n) (B : Mat m (n-r))
    (hmin : deletionSingular θ A ≤ deletionSingular θ B)
    (hprob : (stdGaussian (Space (n-r))).real (ProjectionGood θ B δ)ᶜ ≤
      projectionFailure θ (n-r) r δ) :
    normalizedDeletion θ A ≤ deterministicBound θ n r δ := by
  have hd : 1 ≤ n-r := by omega
  have hn : 1 ≤ n := by omega
  obtain ⟨g,hg⟩ := projectionGood_nonempty_of_probability_bound θ δ B
    (deterministicFailure θ n r δ) hfail hprob
  exact normalizedDeletion_le_of_projectionGood θ hθ m n (n-r) hm hn hd A B hmin δ hδ g hg

end NLA.IE22
