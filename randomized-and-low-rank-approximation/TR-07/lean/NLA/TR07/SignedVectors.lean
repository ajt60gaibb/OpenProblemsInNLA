import NLA.TR07.Covariance

/-! Exact fixed-sparsity identities and the regularized diagonal majorant. -/
noncomputable section
open scoped BigOperators
open Matrix
attribute [local instance] Classical.propDecidable
namespace NLA.TR07

variable {α : Type*} [Fintype α] {k s : ℕ}

def SignedVector (s : ℕ) (v : Vec k) : Prop :=
  (∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1) ∧
    (Finset.univ.filter fun i => v i ≠ 0).card = s

theorem SignedSparse.column {n : ℕ} {M : Mat k n} (h : SignedSparse s M) (j : Fin n) :
    SignedVector s (WithLp.toLp 2 (fun i => M i j)) := ⟨fun i => h.1 i j, h.2 j⟩

theorem SignedVector.sq_eq {v : Vec k} (h : SignedVector s v) (i : Fin k) :
    v i ^ 2 = if v i ≠ 0 then 1 else 0 := by
  rcases h.1 i with he | he | he <;> simp [he]

theorem SignedVector.norm_sq {v : Vec k} (h : SignedVector s v) : ‖v‖ ^ 2 = s := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [h.sq_eq]
  rw [← Finset.sum_filter]
  simp [h.2]

theorem SignedVector.coordinate_sq_le {v : Vec k} (h : SignedVector s v) (i : Fin k) :
    v i ^ 2 ≤ 1 := by rw [h.sq_eq]; split_ifs <;> norm_num

theorem SignedVector.dot_sq_le {v : Vec k} (h : SignedVector s v) (x : Fin k → ℝ) :
    (⇑v ⬝ᵥ x) ^ 2 ≤ (s : ℝ) * ∑ i, v i ^ 2 * x i ^ 2 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => if v i ≠ 0 then (1 : ℝ) else 0) (fun i => v i * x i)
  have hleft : (∑ i, (if v i ≠ 0 then (1 : ℝ) else 0) * (v i * x i)) = ⇑v ⬝ᵥ x := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : v i = 0 <;> simp [hi]
  have hfirst : (∑ i, (if v i ≠ 0 then (1 : ℝ) else 0) ^ 2) = s := by
    calc
      _ = ∑ i, v i ^ 2 := by apply Finset.sum_congr rfl; intro i _; rw [h.sq_eq]; split_ifs <;> norm_num
      _ = s := by rw [← EuclideanSpace.real_norm_sq_eq, h.norm_sq]
  simpa only [hleft, hfirst, mul_pow] using hc

def incidence (p : Law α) (u : α → Vec k) (i : Fin k) : ℝ :=
  p.expect (fun a => u a i ^ 2)

theorem incidence_nonneg (p : Law α) (u : α → Vec k) (i : Fin k) :
    0 ≤ incidence p u i := p.expect_nonneg fun _ => sq_nonneg _

theorem incidence_le_one (p : Law α) (u : α → Vec k) (hu : ∀ a, SignedVector s (u a)) (i : Fin k) :
    incidence p u i ≤ 1 := p.expect_le_const fun a => (hu a).coordinate_sq_le i

theorem sum_incidence (p : Law α) (u : α → Vec k) (hu : ∀ a, SignedVector s (u a)) :
    ∑ i, incidence p u i = s := by
  unfold incidence
  rw [← p.expect_sum]
  simp_rw [← EuclideanSpace.real_norm_sq_eq, fun a => (hu a).norm_sq]
  exact p.expect_const _

def regDiagonal (p : Law α) (u : α → Vec k) (i : Fin k) : ℝ := incidence p u i + (k : ℝ)⁻¹

theorem regDiagonal_pos (p : Law α) (u : α → Vec k) (hk : 0 < k) (i : Fin k) :
    0 < regDiagonal p u i := add_pos_of_nonneg_of_pos (incidence_nonneg p u i) (by positivity)

theorem sum_regDiagonal (p : Law α) (u : α → Vec k) (hu : ∀ a, SignedVector s (u a)) (hk : 0 < k) :
    ∑ i, regDiagonal p u i = (s : ℝ) + 1 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp [regDiagonal, Finset.sum_add_distrib, sum_incidence p u hu, hk']

theorem covariance_sparse_cap (p : Law α) (u : α → Vec k) (hu : ∀ a, SignedVector s (u a)) :
    ((s : ℝ) • diagonal (incidence p u) - covariance p u).PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (isHermitian_diagonal_of_self_adjoint _ (funext fun _ => IsSelfAdjoint.all _)).smul
      (IsSelfAdjoint.all _) |>.sub (covariance_psd p u).isHermitian
  · intro x
    have hb := p.expect_mono (fun a => (hu a).dot_sq_le x)
    rw [p.expect_const_mul, p.expect_sum] at hb
    simp_rw [p.expect_mul_const] at hb
    rw [← covariance_quadratic] at hb
    simp only [star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
      smul_eq_mul]
    apply sub_nonneg.mpr
    convert hb using 1 <;>
      first | rfl | simp [mulVec_diagonal, dotProduct, incidence, pow_two, mul_comm, mul_assoc]

theorem covariance_regularized_cap (p : Law α) (u : α → Vec k)
    (hu : ∀ a, SignedVector s (u a)) :
    ((s : ℝ) • diagonal (regDiagonal p u) - covariance p u).PosSemidef := by
  have hd : (diagonal (fun _ : Fin k => (s : ℝ) * (k : ℝ)⁻¹)).PosSemidef := by
    apply PosSemidef.diagonal
    intro i
    positivity
  convert (covariance_sparse_cap p u hu).add hd using 1
  ext i j
  by_cases h : i = j
  · simp [h, regDiagonal, mul_add]
    ring
  · simp [h]

end NLA.TR07
