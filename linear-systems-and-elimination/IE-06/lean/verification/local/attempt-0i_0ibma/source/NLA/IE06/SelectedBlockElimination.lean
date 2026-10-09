/- Exact selected-block coordinates of the actual elimination rows.
Preimplementation contract and independent approval are recorded in reviews/.
-/
import NLA.IE06.GaussianPivotConditioning
import NLA.IE06.EliminationBlock
import NLA.IE06.KyFan

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
noncomputable section
open Matrix WithLp
open scoped BigOperators
namespace NLA.IE06.SelectedBlockElimination
open GaussianPivotConditioning

/-- Nonzero pivots alone suffice for exact annihilation; no size bound is used. -/
theorem annihilates_of_pivots {n : ℕ} (A : Mat n) (p : PivotPath n)
    (s : ℕ) (hp : ∀ k : Fin n, k.val < s → trajectory A p k.val (p k) k ≠ 0)
    (i j : Fin n) (hj : j.val < s) :
    (Matrix.of (eliminationRows A p s) * Matrix.of A) i j = 0 := by
  induction s generalizing i j with
  | zero => omega
  | succ s ih =>
    by_cases hs : s < n
    · rw [eliminationRows,dif_pos hs,eliminationStep_mul_apply]
      split_ifs with hi
      · by_cases hjs : j.val < s
        · rw [ih (fun k hk => hp k (by omega)) _ j hjs,
            ih (fun k hk => hp k (by omega)) _ j hjs]; ring
        · have heq : j = ⟨s,hs⟩ := Fin.ext (by change j.val = s; omega)
          subst j
          rw [eliminationRows_mul A p s _ _ le_rfl,eliminationRows_mul A p s _ _ le_rfl]
          simp only [rowSwap,Equiv.swap_apply_left]
          rw [div_mul_cancel₀ _ (hp ⟨s,hs⟩ (by simp)),sub_self]
      · rfl
    · rw [eliminationRows,dif_neg hs]
      exact congrFun (congrFun (Matrix.zero_mul (Matrix.of A)) i) j

theorem det_ne_zero_of_pivots {t : ℕ} (T : Mat t)
    (hu : ∀ j : Fin t, pivotValue T j ≠ 0) : T.det ≠ 0 := by
  let C : Matrix (Fin t) (Fin t) ℝ := fun i j => eliminationRows T id i.val i j
  have he : C * Matrix.of T = Matrix.of (upperMatrix T) := by
    ext i j
    change (Matrix.of (eliminationRows T id i.val) * Matrix.of T) i j = upperRow T i j
    by_cases hij : i.val ≤ j.val
    · exact eliminationRows_mul T id i.val i j hij
    · rw [annihilates_of_pivots T id i.val (fun j _ => hu j) i j (by omega)]
      exact (trajectory_inactive_column T id i.val i j (by omega)).symm
  have hd : (C * Matrix.of T).det ≠ 0 := by rw [he]; exact upperMatrix_det_ne_zero T hu
  rw [Matrix.det_mul] at hd
  exact (mul_ne_zero_iff.mp hd).2

/-- Exactly the first t actual pivots are nonzero; later columns are unrestricted. -/
def PrefixNonzero {n t : ℕ} (ht : t ≤ n) (A : Mat n) : Prop :=
  ∀ j : Fin t, firstTrajectory A j.val (firstPath A (Fin.castLE ht j)) (Fin.castLE ht j) ≠ 0

theorem prefixNonzero_of_det_ne_zero {n t : ℕ} (ht : t ≤ n) (A : Mat n)
    (hA : A.det ≠ 0) : PrefixNonzero ht A := by
  intro j
  rw [← trajectory_firstPath_eq_proved]
  exact (firstPath_admissible_proved A hA (Fin.castLE ht j)).2.1

/-- The fixed-fiber Good condition supplies exactly the required prefix premise. -/
theorem prefixNonzero_of_good {n t : ℕ} (ht : t ≤ n) (A : Mat n)
    (hg : Good (selectedBlock ht (pivotOrder ht A) A)) : PrefixNonzero ht A := by
  intro j
  rw [firstTrajectory_pivot_entry ht A j j le_rfl]
  exact hg.1 j

/-- The selected original row block is nonsingular, including the empty block. -/
theorem selectedBlock_det_ne_zero_of_prefix {n t : ℕ} (ht : t ≤ n) (A : Mat n)
    (hp : PrefixNonzero ht A) : (selectedBlock ht (pivotOrder ht A) A).det ≠ 0 := by
  apply det_ne_zero_of_pivots
  intro j
  have hv := firstTrajectory_pivot_entry ht A j j le_rfl
  exact fun hz => hp j (hv.trans hz)

theorem selectedBlock_det_ne_zero {n t : ℕ} (ht : t ≤ n) (A : Mat n)
    (hA : A.det ≠ 0) : (selectedBlock ht (pivotOrder ht A) A).det ≠ 0 :=
  selectedBlock_det_ne_zero_of_prefix ht A (prefixNonzero_of_det_ne_zero ht A hA)

theorem swap_active {n : ℕ} (k p i : Fin n) (hp : k ≤ p) (hi : k ≤ i) :
    k ≤ Equiv.swap k p i := by
  by_cases hik : i = k
  · subst i; simpa using hp
  by_cases hip : i = p
  · subst i; simp
  simpa [Equiv.swap_apply_of_ne_of_ne hik hip] using hi

/-- On still-unselected original coordinates the active left operator is exactly I. -/
theorem remaining_coordinates {n : ℕ} (A : Mat n) (p : PivotPath n)
    (hp : ∀ k, k ≤ p k) (s : ℕ) (i q : Fin n) (hi : s ≤ i.val) (hq : s ≤ q.val) :
    eliminationRows A p s i (rowLabels p s q) = if i = q then 1 else 0 := by
  induction s generalizing i q with
  | zero => simp only [eliminationRows,rowLabels,Equiv.refl_apply,Matrix.one_apply]
  | succ s ih =>
    have hs : s < n := by omega
    let k : Fin n := ⟨s,hs⟩
    have his : k < i := hi
    have hqs : k < q := hq
    have hi' := swap_active k (p k) i (hp k) his.le
    have hq' := swap_active k (p k) q (hp k) hqs.le
    have hpq : p k ≠ Equiv.swap k (p k) q := by
      intro h
      have he : Equiv.swap k (p k) k = Equiv.swap k (p k) q := by
        simpa only [Equiv.swap_apply_left] using h
      have heq := (Equiv.swap k (p k)).injective he
      exact (ne_of_lt hqs) heq
    rw [eliminationRows,dif_pos hs,rowLabels_succ p k]
    change eliminationStep (trajectory A p s) (eliminationRows A p s) k (p k) i
      (rowLabels p s (Equiv.swap k (p k) q)) = _
    simp only [eliminationStep,his,if_true,rowSwap,Equiv.swap_apply_left]
    rw [ih _ _ hi' hq',ih _ _ (hp k) hq',if_neg hpq]
    simp [(Equiv.swap k (p k)).injective.eq_iff]

/-- An active row's original identity coordinate was not selected. -/
theorem active_label_not_selected {n t : ℕ} (ht : t ≤ n) (A : Mat n)
    (i : Fin n) (hi : t ≤ i.val) :
    rowLabels (firstPath A) t i ∉ Set.range (pivotOrder ht A) := by
  rintro ⟨j,hj⟩
  have he := (rowLabels (firstPath A) t).injective hj
  have heval := congrArg Fin.val he
  have := j.isLt
  change j.val = i.val at heval
  omega

/-- Exact reconstruction of an active row from its selected coordinates. -/
theorem row_reconstruction {n t : ℕ} (ht : t ≤ n) (A : Mat n)
    (i : Fin n) (hi : t ≤ i.val) (j : Fin n) :
    eliminationRows A (firstPath A) t i j =
      (if j = rowLabels (firstPath A) t i then 1 else 0) +
      ∑ a : Fin t, eliminationRows A (firstPath A) t i (pivotOrder ht A a) *
        (if j = pivotOrder ht A a then 1 else 0) := by
  classical
  let π := pivotOrder ht A
  let p := firstPath A
  let e : Fin n → ℝ := fun j => eliminationRows A (firstPath A) t i j
  change e j = (if j = rowLabels p t i then 1 else 0) +
    ∑ a : Fin t, e (π a) * (if j = π a then 1 else 0)
  have hp : ∀ k : Fin n, k ≤ p k := fun k =>
    (firstPivotIndex_spec_proved (firstTrajectory A k.val) k).1
  have hlabel := active_label_not_selected ht A i hi
  by_cases hj : j ∈ Set.range π
  · obtain ⟨a,rfl⟩ := hj
    have hne : π a ≠ rowLabels p t i := fun h => hlabel ⟨a,h⟩
    simp only [hne,if_false,zero_add]
    have he (b : Fin t) : (if π a = π b then (1:ℝ) else 0) =
        if a = b then 1 else 0 := by simp only [π.injective.eq_iff]
    simp_rw [he]
    simp
  · have hnone (a : Fin t) : j ≠ π a := fun h => hj ⟨a,h.symm⟩
    simp only [hnone,if_false,mul_zero,Finset.sum_const_zero,add_zero]
    let q := (rowLabels p t).symm j
    have hq : t ≤ q.val := by
      by_contra! hqt
      apply hj
      refine ⟨⟨q.val,hqt⟩,?_⟩
      exact (rowLabels p t).apply_symm_apply j
    have heq : j = rowLabels p t q := ((rowLabels p t).apply_symm_apply j).symm
    rw [heq]
    change eliminationRows A p t i (rowLabels p t q) = _
    rw [remaining_coordinates A p hp t i q hi hq]
    simp [(rowLabels p t).injective.eq_iff,eq_comm]

/-- The coefficients at selected labels solve the actual leading block equation. -/
theorem selected_coefficients_mul {n t : ℕ} (ht : t ≤ n) (A : Mat n)
    (hp : PrefixNonzero ht A) (i : Fin n) (hi : t ≤ i.val) :
    (fun a : Fin t => eliminationRows A (firstPath A) t i (pivotOrder ht A a)) ᵥ*
      selectedBlock ht (pivotOrder ht A) A =
      -prefixRows ht A (rowLabels (firstPath A) t i) := by
  funext k
  have hp' (j : Fin n) (hj : j.val < t) :
      trajectory A (firstPath A) j.val (firstPath A j) j ≠ 0 := by
    have h := hp ⟨j.val,hj⟩
    rw [← trajectory_firstPath_eq_proved] at h
    exact h
  have hz := annihilates_of_pivots A (firstPath A) t hp' i (Fin.castLE ht k) k.isLt
  have he : (Matrix.of (eliminationRows A (firstPath A) t) * Matrix.of A) i (Fin.castLE ht k) =
      A (rowLabels (firstPath A) t i) (Fin.castLE ht k) +
        ∑ a : Fin t, eliminationRows A (firstPath A) t i (pivotOrder ht A a) *
          A (pivotOrder ht A a) (Fin.castLE ht k) := by
    simp only [Matrix.mul_apply,Matrix.of_apply]
    conv_lhs =>
      arg 2
      ext j
      rw [row_reconstruction ht A i hi j]
    simp_rw [add_mul,Finset.sum_mul]
    rw [Finset.sum_add_distrib]
    congr 1
    · simp [ite_mul]
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      simp [ite_mul]
  rw [he] at hz
  change (∑ a : Fin t, eliminationRows A (firstPath A) t i (pivotOrder ht A a) *
    A (pivotOrder ht A a) (Fin.castLE ht k)) = -A (rowLabels (firstPath A) t i) (Fin.castLE ht k)
  linarith

theorem selected_coefficients {n t : ℕ} (ht : t ≤ n) (A : Mat n)
    (hp : PrefixNonzero ht A) (i : Fin n) (hi : t ≤ i.val) :
    (fun a : Fin t => eliminationRows A (firstPath A) t i (pivotOrder ht A a)) =
      -(prefixRows ht A (rowLabels (firstPath A) t i) ᵥ*
        (selectedBlock ht (pivotOrder ht A) A)⁻¹) := by
  have h := congrArg (fun z : Fin t → ℝ => z ᵥ* (selectedBlock ht (pivotOrder ht A) A)⁻¹)
    (selected_coefficients_mul ht A hp i hi)
  rw [Matrix.vecMul_vecMul,Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (selectedBlock_det_ne_zero_of_prefix ht A hp)),Matrix.vecMul_one] at h
  simpa only [Matrix.neg_vecMul] using h

/-- Literal original-coordinate elimination row under only prefix nonzero pivots. -/
theorem row_eq_selected_inverse_of_prefix {n t : ℕ} (ht : t ≤ n) (A : Mat n)
    (hp : PrefixNonzero ht A) (i : Fin n) (hi : t ≤ i.val) (j : Fin n) :
    eliminationRows A (firstPath A) t i j =
      (if j = rowLabels (firstPath A) t i then 1 else 0) -
      ∑ a : Fin t,
        (prefixRows ht A (rowLabels (firstPath A) t i) ᵥ*
          (selectedBlock ht (pivotOrder ht A) A)⁻¹) a *
        (if j = pivotOrder ht A a then 1 else 0) := by
  rw [row_reconstruction ht A i hi j]
  have hc := selected_coefficients ht A hp i hi
  have hc' (a : Fin t) := congrFun hc a
  simp only [Pi.neg_apply] at hc'
  simp_rw [hc',neg_mul]
  rw [Finset.sum_neg_distrib]
  rfl

theorem row_eq_selected_inverse {n t : ℕ} (ht : t ≤ n) (A : Mat n)
    (hA : A.det ≠ 0) (i : Fin n) (hi : t ≤ i.val) (j : Fin n) :
    eliminationRows A (firstPath A) t i j =
      (if j = rowLabels (firstPath A) t i then 1 else 0) -
      ∑ a : Fin t,
        (prefixRows ht A (rowLabels (firstPath A) t i) ᵥ*
          (selectedBlock ht (pivotOrder ht A) A)⁻¹) a *
        (if j = pivotOrder ht A a then 1 else 0) :=
  row_eq_selected_inverse_of_prefix ht A (prefixNonzero_of_det_ne_zero ht A hA) i hi j

/-- Disjoint original-label coordinates give an exact Euclidean square norm. -/
theorem selected_embedding_sq {n t : ℕ} (π : Fin t ↪ Fin n) (label : Fin n)
    (hl : label ∉ Set.range π) (c : Fin t → ℝ) :
    (∑ j : Fin n, ((if j = label then (1:ℝ) else 0) -
      ∑ a : Fin t, c a * (if j = π a then 1 else 0))^2) = 1 + ∑ a : Fin t, (c a)^2 := by
  classical
  have he (j : Fin n) :
      ((if j = label then (1:ℝ) else 0) -
        ∑ a : Fin t, c a * (if j = π a then 1 else 0))^2 =
      (if j = label then (1:ℝ) else 0) +
        ∑ a : Fin t, (c a)^2 * (if j = π a then 1 else 0) := by
    by_cases hj : j = label
    · subst j
      have hne (a : Fin t) : label ≠ π a := fun h => hl ⟨a,h.symm⟩
      simp [hne]
    · by_cases hp : j ∈ Set.range π
      · obtain ⟨a,rfl⟩ := hp
        simp [hj,π.injective.eq_iff]
      · have hne (a : Fin t) : j ≠ π a := fun h => hp ⟨a,h.symm⟩
        simp [hj,hne]
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_comm]
  simp

/-- Exact norm identity for an active row, valid under only prefix nonzero pivots. -/
theorem row_norm_sq_of_prefix {n t : ℕ} (ht : t ≤ n) (A : Mat n)
    (hp : PrefixNonzero ht A) (i : Fin n) (hi : t ≤ i.val) :
    ‖(toLp 2 (eliminationRows A (firstPath A) t i) : EuclideanSpace ℝ (Fin n))‖^2 =
      1 + ‖(toLp 2 (prefixRows ht A (rowLabels (firstPath A) t i) ᵥ*
        (selectedBlock ht (pivotOrder ht A) A)⁻¹) : EuclideanSpace ℝ (Fin t))‖^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq]
  simp_rw [row_eq_selected_inverse_of_prefix ht A hp i hi]
  exact selected_embedding_sq (pivotOrder ht A) (rowLabels (firstPath A) t i)
    (active_label_not_selected ht A i hi) _

theorem row_norm_sq {n t : ℕ} (ht : t ≤ n) (A : Mat n)
    (hA : A.det ≠ 0) (i : Fin n) (hi : t ≤ i.val) :
    ‖(toLp 2 (eliminationRows A (firstPath A) t i) : EuclideanSpace ℝ (Fin n))‖^2 =
      1 + ‖(toLp 2 (prefixRows ht A (rowLabels (firstPath A) t i) ᵥ*
        (selectedBlock ht (pivotOrder ht A) A)⁻¹) : EuclideanSpace ℝ (Fin t))‖^2 :=
  row_norm_sq_of_prefix ht A (prefixNonzero_of_det_ne_zero ht A hA) i hi

/- Every local declaration is audited transitively under kernel policy. -/
#assert_trust kernel annihilates_of_pivots
#print axioms annihilates_of_pivots
#assert_trust kernel det_ne_zero_of_pivots
#print axioms det_ne_zero_of_pivots
#assert_trust kernel PrefixNonzero
#print axioms PrefixNonzero
#assert_trust kernel prefixNonzero_of_det_ne_zero
#print axioms prefixNonzero_of_det_ne_zero
#assert_trust kernel prefixNonzero_of_good
#print axioms prefixNonzero_of_good
#assert_trust kernel selectedBlock_det_ne_zero_of_prefix
#print axioms selectedBlock_det_ne_zero_of_prefix
#assert_trust kernel selectedBlock_det_ne_zero
#print axioms selectedBlock_det_ne_zero
#assert_trust kernel swap_active
#print axioms swap_active
#assert_trust kernel remaining_coordinates
#print axioms remaining_coordinates
#assert_trust kernel active_label_not_selected
#print axioms active_label_not_selected
#assert_trust kernel row_reconstruction
#print axioms row_reconstruction
#assert_trust kernel selected_coefficients_mul
#print axioms selected_coefficients_mul
#assert_trust kernel selected_coefficients
#print axioms selected_coefficients
#assert_trust kernel row_eq_selected_inverse_of_prefix
#print axioms row_eq_selected_inverse_of_prefix
#assert_trust kernel row_eq_selected_inverse
#print axioms row_eq_selected_inverse
#assert_trust kernel selected_embedding_sq
#print axioms selected_embedding_sq
#assert_trust kernel row_norm_sq_of_prefix
#print axioms row_norm_sq_of_prefix
#assert_trust kernel row_norm_sq
#print axioms row_norm_sq

end NLA.IE06.SelectedBlockElimination
