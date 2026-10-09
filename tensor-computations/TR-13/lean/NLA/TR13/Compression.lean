import NLA.TR13.Definitions
import Mathlib.LinearAlgebra.Matrix.Rank

noncomputable section
open scoped BigOperators
namespace NLA.TR13

theorem exists_index_sum (k n u : ℕ) (hn : 0 < n) (hu : u ≤ k * (n - 1)) :
    ∃ i : Fin k → Fin n, (∑ j, (i j).val) = u := by
  induction k generalizing u with
  | zero =>
      have : u = 0 := by simpa using hu
      subst u
      exact ⟨Fin.elim0, by simp⟩
  | succ k ih =>
      have hc : min u (n - 1) < n := lt_of_le_of_lt (min_le_right _ _) (by omega)
      have hr : u - min u (n - 1) ≤ k * (n - 1) := by
        simp only [Nat.succ_mul] at hu
        omega
      obtain ⟨i, hi⟩ := ih (u - min u (n - 1)) hr
      refine ⟨Fin.cons ⟨min u (n - 1), hc⟩ i, ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [hi]
      omega

def sumRepresentative (k n : ℕ) (hn : 0 < n) (u : Fin (k * (n - 1) + 1)) :
    Fin k → Fin n :=
  (exists_index_sum k n u hn (by omega)).choose

theorem sum_sumRepresentative (k n : ℕ) (hn : 0 < n)
    (u : Fin (k * (n - 1) + 1)) :
    (∑ j, (sumRepresentative k n hn u j).val) = u.val :=
  (exists_index_sum k n u hn (by omega)).choose_spec

def joinIndex {k n : ℕ} (I : Fin k → Fin n) (j : Fin n) (J : Fin k → Fin n) :
    Fin (2 * k + 1) → Fin n :=
  fun t => Fin.addCases I (fun t : Fin (k + 1) => Fin.cases j J t) (Fin.cast (by omega) t)

theorem sum_joinIndex {k n : ℕ} (I : Fin k → Fin n) (j : Fin n)
    (J : Fin k → Fin n) :
    (∑ t, (joinIndex I j J t).val) = (∑ t, (I t).val) + j.val + ∑ t, (J t).val := by
  have he : (∑ t : Fin (2 * k + 1), (joinIndex I j J t).val) =
      ∑ t : Fin (k + (k + 1)), (Fin.addCases I (fun t : Fin (k + 1) => Fin.cases j J t) t : Fin n).val :=
    Fintype.sum_equiv (finCongr (by omega)) _ _ (fun _ => rfl)
  rw [he, Fin.sum_univ_add, Fin.sum_univ_succ]
  simp [add_assoc]

def leftPosition (k : ℕ) (i : Fin k) : Fin (2 * k + 1) :=
  (Fin.castAdd (k + 1) i).cast (by omega)

def middlePosition (k : ℕ) : Fin (2 * k + 1) :=
  (Fin.natAdd k (0 : Fin (k + 1))).cast (by omega)

def rightPosition (k : ℕ) (i : Fin k) : Fin (2 * k + 1) :=
  (Fin.natAdd k i.succ).cast (by omega)

theorem pureTensor_joinIndex {k n : ℕ} (v : Fin (2 * k + 1) → Fin n → ℂ)
    (I : Fin k → Fin n) (j : Fin n) (J : Fin k → Fin n) :
    pureTensor v (joinIndex I j J) =
      (∏ t, v (leftPosition k t) (I t)) * v (middlePosition k) j *
      ∏ t, v (rightPosition k t) (J t) := by
  unfold pureTensor
  have he : (∏ t : Fin (2 * k + 1), v t (joinIndex I j J t)) =
      ∏ t : Fin (k + (k + 1)),
        v (t.cast (by omega)) (Fin.addCases I (fun t : Fin (k + 1) => Fin.cases j J t) t) :=
    Fintype.prod_equiv (finCongr (by omega)) _ _ (fun _ => by simp [joinIndex])
  rw [he, Fin.prod_univ_add, Fin.prod_univ_succ]
  simp [leftPosition, middlePosition, rightPosition, mul_assoc]

def middleIndex (n : ℕ) (hn : 0 < n) (j : Fin 3) : Fin n :=
  ⟨j.val * ((n - 1) / 2), by
    have hj : j.val ≤ 2 := by omega
    have hs := Nat.mul_div_le (n - 1) 2
    have hjm := Nat.mul_le_mul_right ((n - 1) / 2) hj
    omega⟩

def compressedTensor (k n : ℕ) (hn : 0 < n) (T : Tensor (2 * k + 1) n) :
    Fin (k * (n - 1) + 1) → Fin 3 → Fin (k * (n - 1) + 1) → ℂ :=
  fun u j v => T (joinIndex (sumRepresentative k n hn u) (middleIndex n hn j)
    (sumRepresentative k n hn v))

theorem compressedTensor_pure (k n : ℕ) (hn : 0 < n)
    (v : Fin (2 * k + 1) → Fin n → ℂ) :
    ∃ (c : Fin 3 → ℂ) (a b : Fin (k * (n - 1) + 1) → ℂ),
      ∀ u j w, compressedTensor k n hn (pureTensor v) u j w = c j * a u * b w := by
  refine ⟨fun j => v (middlePosition k) (middleIndex n hn j),
    fun u => ∏ t, v (leftPosition k t) (sumRepresentative k n hn u t),
    fun w => ∏ t, v (rightPosition k t) (sumRepresentative k n hn w t), ?_⟩
  intro u j w
  dsimp [compressedTensor]
  rw [pureTensor_joinIndex]
  ring

theorem compressedTensor_hankel (k n : ℕ) (hn : 0 < n)
    (h : Moments (2 * k + 1) n)
    (u w : Fin (k * (n - 1) + 1)) (j : Fin 3) :
    compressedTensor k n hn (hankel h) u j w =
      h ⟨u.val + j.val * ((n - 1) / 2) + w.val, by
        have hu := u.isLt
        have hw := w.isLt
        have hj := (middleIndex n hn j).isLt
        change j.val * ((n - 1) / 2) < n at hj
        have hnn : n - 1 + 1 = n := by omega
        nlinarith⟩ := by
  unfold compressedTensor hankel
  congr 1
  apply Fin.ext
  change (∑ t, (joinIndex (sumRepresentative k n hn u) (middleIndex n hn j)
    (sumRepresentative k n hn w) t).val) =
      u.val + j.val * ((n - 1) / 2) + w.val
  rw [sum_joinIndex, sum_sumRepresentative, sum_sumRepresentative]
  rfl

end NLA.TR13
