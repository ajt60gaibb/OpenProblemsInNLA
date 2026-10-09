import NLA.TR13.Koszul
import NLA.TR13.MatrixCertificate

noncomputable section
open scoped BigOperators
open Matrix

namespace NLA.TR13

def lowerShift (a d : ℕ) : Matrix (Fin a) (Fin a) ℂ :=
  fun i j => if j.val + d = i.val then 1 else 0

def upperShift (a d : ℕ) : Matrix (Fin a) (Fin a) ℂ :=
  fun i j => if i.val + d = j.val then 1 else 0

theorem lowerShift_mulVec (a d : ℕ) (x : Fin a → ℂ) (i : Fin a) :
    (lowerShift a d *ᵥ x) i =
      if h : d ≤ i.val then x ⟨i.val - d, by omega⟩ else 0 := by
  classical
  rw [Matrix.mulVec, dotProduct]
  by_cases h : d ≤ i.val
  · rw [dif_pos h]
    let j : Fin a := ⟨i.val-d, by omega⟩
    rw [Finset.sum_eq_single j]
    · simp [lowerShift, j, Nat.sub_add_cancel h]
    · intro k _ hk
      have hh : k.val + d ≠ i.val := by
        intro hh
        apply hk
        apply Fin.ext
        simp only [j]
        omega
      simp [lowerShift, hh]
    · simp
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro j _
    have hh : j.val + d ≠ i.val := by omega
    simp [lowerShift, hh]

theorem upperShift_mulVec (a d : ℕ) (x : Fin a → ℂ) (i : Fin a) :
    (upperShift a d *ᵥ x) i =
      if h : i.val + d < a then x ⟨i.val+d, h⟩ else 0 := by
  classical
  rw [Matrix.mulVec, dotProduct]
  by_cases h : i.val + d < a
  · rw [dif_pos h]
    let j : Fin a := ⟨i.val+d, h⟩
    rw [Finset.sum_eq_single j]
    · simp [upperShift, j]
    · intro k _ hk
      have hh : i.val + d ≠ k.val := by
        intro hh
        apply hk
        exact Fin.ext hh.symm
      simp [upperShift, hh]
    · simp
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro j _
    have hh : i.val + d ≠ j.val := by omega
    simp [upperShift, hh]

def spikeB (a s : ℕ) : Matrix (Fin a) (Fin a) ℂ := lowerShift a s
def spikeC (a s : ℕ) : Matrix (Fin a) (Fin a) ℂ :=
  lowerShift a (2*s) + upperShift a (a-s)

theorem spike_comm_first {a s : ℕ} (ha : 2*s ≤ a) (x : Fin a → ℂ)
    (i : Fin a) (hi : i.val < s) :
    (spikeC a s *ᵥ (spikeB a s *ᵥ x)) i -
        (spikeB a s *ᵥ (spikeC a s *ᵥ x)) i =
      x ⟨a-2*s+i.val, by omega⟩ := by
  have hs : s ≤ a := by omega
  have h1 : ¬2*s ≤ i.val := by omega
  have h2 : i.val + (a-s) < a := by omega
  have h3 : s ≤ i.val + (a-s) := by omega
  have h4 : ¬s ≤ i.val := by omega
  simp [-Matrix.mulVec_mulVec, spikeB, spikeC, Matrix.add_mulVec, lowerShift_mulVec, upperShift_mulVec,
    h1, h2, h3, h4]
  congr 1
  apply Fin.ext
  dsimp only
  omega

theorem spike_comm_second {a s : ℕ} (ha : 2*s ≤ a) (x : Fin a → ℂ)
    (i : Fin a) (hi : s ≤ i.val) (hi' : i.val < 2*s) :
    (spikeC a s *ᵥ (spikeB a s *ᵥ x)) i -
        (spikeB a s *ᵥ (spikeC a s *ᵥ x)) i =
      -x ⟨a-2*s+i.val, by omega⟩ := by
  have hs : s ≤ a := by omega
  have h1 : ¬2*s ≤ i.val := by omega
  have h2 : ¬i.val + (a-s) < a := by omega
  have h3 : ¬2*s ≤ i.val-s := by omega
  have h4 : i.val-s+(a-s) < a := by omega
  simp [-Matrix.mulVec_mulVec, spikeB, spikeC, Matrix.add_mulVec, lowerShift_mulVec, upperShift_mulVec,
    h1, h2, hi, h3, h4]
  congr 2
  omega

theorem koszul_identity_mulVec_zero {a : ℕ} (B C : Matrix (Fin a) (Fin a) ℂ)
    (x : KoszulIndex a → ℂ) (i : Fin a) :
    (koszul ![1, B, C] *ᵥ x) (0,i) =
      -(B *ᵥ fun j => x (0,j)) i + x (1,i) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three]
  change (∑ j, -B i j * x (0,j)) +
    (∑ j, (1 : Matrix (Fin a) (Fin a) ℂ) i j * x (1,j)) +
    (∑ j, (0:ℂ) * x (2,j)) = _
  simp only [neg_mul, Finset.sum_neg_distrib, zero_mul, Finset.sum_const_zero, add_zero]
  congr 1
  exact congrFun (Matrix.one_mulVec (fun j => x (1,j))) i

theorem koszul_identity_mulVec_one {a : ℕ} (B C : Matrix (Fin a) (Fin a) ℂ)
    (x : KoszulIndex a → ℂ) (i : Fin a) :
    (koszul ![1, B, C] *ᵥ x) (1,i) =
      -(C *ᵥ fun j => x (0,j)) i + x (2,i) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three]
  change (∑ j, -C i j * x (0,j)) +
    (∑ j, (0:ℂ) * x (1,j)) +
    (∑ j, (1 : Matrix (Fin a) (Fin a) ℂ) i j * x (2,j)) = _
  simp only [neg_mul, Finset.sum_neg_distrib, zero_mul, Finset.sum_const_zero, add_zero]
  congr 1
  exact congrFun (Matrix.one_mulVec (fun j => x (2,j))) i

theorem koszul_identity_mulVec_two {a : ℕ} (B C : Matrix (Fin a) (Fin a) ℂ)
    (x : KoszulIndex a → ℂ) (i : Fin a) :
    (koszul ![1, B, C] *ᵥ x) (2,i) =
      -(C *ᵥ fun j => x (1,j)) i + (B *ᵥ fun j => x (2,j)) i := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_three]
  change (∑ j, (0:ℂ) * x (0,j)) + (∑ j, -C i j * x (1,j)) +
    (∑ j, B i j * x (2,j)) = _
  simp only [neg_mul, Finset.sum_neg_distrib, zero_mul, Finset.sum_const_zero, zero_add]

theorem spike_koszul_kernel_determined {a s : ℕ} (ha : 2*s ≤ a)
    (x : KoszulIndex a → ℂ)
    (hx : koszul ![1, spikeB a s, spikeC a s] *ᵥ x = 0)
    (hstart : ∀ i : Fin (a-2*s), x (0, ⟨i.val, by omega⟩) = 0) : x = 0 := by
  let z : Fin a → ℂ := fun i => x (0,i)
  have hy (i : Fin a) : x (1,i) = (spikeB a s *ᵥ z) i := by
    have h := congrFun hx (0,i)
    rw [koszul_identity_mulVec_zero] at h
    change -(spikeB a s *ᵥ z) i + x (1,i) = 0 at h
    linear_combination h
  have hz (i : Fin a) : x (2,i) = (spikeC a s *ᵥ z) i := by
    have h := congrFun hx (1,i)
    rw [koszul_identity_mulVec_one] at h
    change -(spikeC a s *ᵥ z) i + x (2,i) = 0 at h
    linear_combination h
  have hcomm (i : Fin a) :
      (spikeC a s *ᵥ (spikeB a s *ᵥ z)) i -
        (spikeB a s *ᵥ (spikeC a s *ᵥ z)) i = 0 := by
    have h := congrFun hx (2,i)
    rw [koszul_identity_mulVec_two] at h
    simp only [hy, hz, Pi.zero_apply] at h
    linear_combination -h
  have hzero : z = 0 := by
    funext j
    by_cases hj : j.val < a-2*s
    · exact hstart ⟨j.val, hj⟩
    · let i : Fin a := ⟨j.val-(a-2*s), by omega⟩
      have hi : i.val < 2*s := by dsimp [i]; omega
      have he : (⟨a-2*s+i.val, by omega⟩ : Fin a) = j := by
        apply Fin.ext
        dsimp [i]
        omega
      by_cases hi' : i.val < s
      · have h := spike_comm_first ha z i hi'
        rw [hcomm, he] at h
        exact h.symm
      · have h := spike_comm_second ha z i (by omega) hi
        rw [hcomm, he] at h
        exact neg_eq_zero.mp h.symm
  funext ⟨i,j⟩
  fin_cases i
  · exact congrFun hzero j
  · change x (1,j) = 0
    rw [hy, hzero, Matrix.mulVec_zero]
    rfl
  · change x (2,j) = 0
    rw [hz, hzero, Matrix.mulVec_zero]
    rfl

theorem spike_koszul_rank {a s : ℕ} (ha : 2*s ≤ a) :
    2*a + 2*s ≤ (koszul ![1, spikeB a s, spikeC a s]).rank := by
  have h := matrix_rank_ge_sub_of_kernel_coordinates
    (koszul ![1, spikeB a s, spikeC a s])
    (fun i : Fin (a-2*s) => (0, (⟨i.val, by omega⟩ : Fin a)))
    (spike_koszul_kernel_determined ha)
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  omega

end NLA.TR13
