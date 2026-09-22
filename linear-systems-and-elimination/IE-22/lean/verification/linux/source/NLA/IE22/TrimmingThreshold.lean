import NLA.IE22.Definitions

/-! Exact finite threshold attainment, Lipschitz control and a deterministic grid.
Original mathematical proof: Matthew J. Colbrook.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, with AI-agent assistance. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
namespace NLA.IE22
open NLA.IE21

/-- A first-moment bound leaves enough entries below the literal source cutoff. -/
lemma retainedRows_le_small_count (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m : ℕ) (hm : 1 ≤ m) (y : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hmean : (∑ i, y i) / (m : ℝ) ≤ 2) :
    retainedRows θ m ≤ (Finset.univ.filter (fun i => y i ≤ truncationScale θ)).card := by
  classical
  let L := truncationScale θ
  let C := Finset.univ.filter (fun i => y i ≤ L)
  let D := Finset.univ.filter (fun i => ¬y i ≤ L)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hgap : 0 < 1 - θ := sub_pos.mpr hθ.2
  have hL : 0 < L := by dsimp [L, truncationScale]; positivity
  have hLeq : L * (1 - θ) = 2 := by dsimp [L, truncationScale]; field_simp [ne_of_gt hgap]
  have hcard : C.card + D.card = m := by
    simpa [C,D] using Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (fun i => y i ≤ L)
  have hcardR : (C.card : ℝ) + D.card = m := by exact_mod_cast hcard
  have hsum : (D.card : ℝ) * L ≤ ∑ i, y i := by
    calc
      (D.card : ℝ) * L = ∑ i ∈ D, L := by simp
      _ ≤ ∑ i ∈ D, y i := Finset.sum_le_sum (fun i hi => (lt_of_not_ge (Finset.mem_filter.mp hi).2).le)
      _ ≤ ∑ i, y i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ D) (fun i _ _ => hy i)
  have hsum2 := (div_le_iff₀ hmpos).mp hmean
  have hc : θ * (m : ℝ) ≤ C.card := by
    have hD : (D.card : ℝ) * L ≤ m * (L * (1 - θ)) := by rw [hLeq]; nlinarith
    have hD' : (D.card : ℝ) ≤ m * (1 - θ) := by nlinarith
    nlinarith
  have hk := (retainedRows_bounds θ hθ m).2.1
  exact_mod_cast (show (retainedRows θ m : ℝ) ≤ C.card by nlinarith)

theorem bounded_trimming_threshold (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m : ℕ) (hm : 1 ≤ m) (y : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hmean : (∑ i, y i) / (m : ℝ) ≤ 2) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ truncationScale θ ∧
      finiteTrim (retainedRows θ m) y / m = trimDual (retainedRows θ m) y t ∧
      ∀ u : ℝ, 0 ≤ u → trimDual (retainedRows θ m) y u ≤
        trimDual (retainedRows θ m) y t := by
  have hgap : 0 < 1 - θ := sub_pos.mpr hθ.2
  have hL : 0 ≤ truncationScale θ := by unfold truncationScale; positivity
  obtain ⟨t,ht,htL,heq⟩ := finiteTrim_bounded_threshold (retainedRows θ m)
    (retainedRows_le θ hθ m) y hy (truncationScale θ) hL
    (retainedRows_le_small_count θ hθ m hm y hy hmean)
  have heq' : finiteTrim (retainedRows θ m) y / m = trimDual (retainedRows θ m) y t := by
    rw [trimDual_eq_div,heq]
  refine ⟨t,ht,htL,heq',?_⟩
  intro u _
  rw [← heq',trimDual_eq_div]
  exact div_le_div_of_nonneg_right (finiteTrim_sum_dual_le hm _ (retainedRows_le θ hθ m) y u) (Nat.cast_nonneg m)

lemma trimDual_increment {m : ℕ} (hm : 1 ≤ m) (k : ℕ) (hk : k ≤ m)
    (y : Fin m → ℝ) (s t : ℝ) (hst : s ≤ t) :
    -(t-s) ≤ trimDual k y t - trimDual k y s ∧
      trimDual k y t - trimDual k y s ≤ t-s := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hkR : (k : ℝ) ≤ m := by exact_mod_cast hk
  have hinge (i : Fin m) : 0 ≤ max (t-y i) 0 - max (s-y i) 0 ∧
      max (t-y i) 0 - max (s-y i) 0 ≤ t-s := by
    constructor
    · exact sub_nonneg.mpr (max_le_max_right 0 (by linarith))
    · have h := abs_max_sub_max_le_abs (t-y i) (s-y i) 0
      rw [show t-y i-(s-y i)=t-s by ring,abs_of_nonneg (sub_nonneg.mpr hst)] at h
      exact (le_abs_self _).trans h
  have hsum0 : 0 ≤ (∑ i, max (t-y i) 0) - ∑ i, max (s-y i) 0 := by
    rw [← Finset.sum_sub_distrib];exact Finset.sum_nonneg fun i _ => (hinge i).1
  have hsum1 : (∑ i, max (t-y i) 0) - ∑ i, max (s-y i) 0 ≤ m*(t-s) := by
    rw [← Finset.sum_sub_distrib]
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun i _ => (hinge i).2)
  rw [trimDual_eq_div,trimDual_eq_div,← sub_div]
  constructor
  · apply (le_div_iff₀ hmpos).2
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  · apply (div_le_iff₀ hmpos).2
    nlinarith

theorem threshold_lipschitz (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m : ℕ) (hm : 1 ≤ m) (y : Fin m → ℝ) (s t : ℝ) :
    |trimDual (retainedRows θ m) y s - trimDual (retainedRows θ m) y t| ≤ |s - t| := by
  rcases le_total s t with hst|hts
  · rw [abs_sub_comm,abs_sub_comm s t,abs_of_nonneg (sub_nonneg.mpr hst)]
    exact abs_le.mpr (trimDual_increment hm _ (retainedRows_le θ hθ m) y s t hst)
  · rw [abs_of_nonneg (sub_nonneg.mpr hts)]
    exact abs_le.mpr (trimDual_increment hm _ (retainedRows_le θ hθ m) y t s hts)

theorem threshold_grid (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : Finset ℝ, (∀ t ∈ C, t ∈ Icc 0 (truncationScale θ)) ∧
      (C.card : ℝ) ≤ truncationScale θ / δ + 2 ∧
      ∀ t ∈ Icc 0 (truncationScale θ), ∃ s ∈ C, |t - s| ≤ δ := by
  classical
  let L := truncationScale θ
  have hgap : 0 < 1 - θ := sub_pos.mpr hθ.2
  have hL : 0 ≤ L := by dsimp [L,truncationScale]; positivity
  let N := ⌊L/δ⌋₊
  let C := (Finset.range (N+1)).image (fun i : ℕ => (i : ℝ)*δ)
  have hN : (N : ℝ) ≤ L/δ := Nat.floor_le (div_nonneg hL hδ.le)
  refine ⟨C,?_,?_,?_⟩
  · intro s hs
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hs
    have hiN : i ≤ N := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hi
    have hiR : (i : ℝ) ≤ N := by exact_mod_cast hiN
    refine ⟨mul_nonneg (Nat.cast_nonneg i) hδ.le,?_⟩
    exact (le_div_iff₀ hδ).mp (hiR.trans hN)
  · have hcard : C.card ≤ N+1 := (Finset.card_image_le).trans_eq (Finset.card_range (N+1))
    have hcardR : (C.card : ℝ) ≤ N+1 := by exact_mod_cast hcard
    linarith
  · intro t ht
    let i := ⌊t/δ⌋₊
    have hiN : i ≤ N := Nat.floor_mono (div_le_div_of_nonneg_right ht.2 hδ.le)
    have hi : i ∈ Finset.range (N+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hiN)
    refine ⟨(i : ℝ)*δ,Finset.mem_image.mpr ⟨i,hi,rfl⟩,?_⟩
    have hl : (i : ℝ) ≤ t/δ := Nat.floor_le (div_nonneg ht.1 hδ.le)
    have hu : t/δ < (i : ℝ)+1 := (Nat.floor_eq_iff (div_nonneg ht.1 hδ.le)).mp rfl |>.2
    have hl' := (le_div_iff₀ hδ).mp hl
    have hu' := (div_lt_iff₀ hδ).mp hu
    rw [abs_of_nonneg (sub_nonneg.mpr hl')]
    nlinarith

end NLA.IE22
