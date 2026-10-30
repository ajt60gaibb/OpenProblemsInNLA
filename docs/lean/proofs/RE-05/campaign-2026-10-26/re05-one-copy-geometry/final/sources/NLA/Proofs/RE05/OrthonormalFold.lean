import NLA.Proofs.RE05.OrthonormalCore

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open scoped BigOperators

/-- Exactly the normalization branch in the model, including its zero case. -/
def normalizeMatrix {n : ℕ} (A : Square n) : Square n :=
  if NLA.Computation.LinearFamilyQuery.norm n A = 0 then 0
  else fun i k => A i k / NLA.Computation.LinearFamilyQuery.norm n A

theorem matrixVector_normalize {n : ℕ} (A : Square n) :
    matrixVector (normalizeMatrix A) = ‖matrixVector A‖⁻¹ • matrixVector A := by
  unfold normalizeMatrix
  rw [← matrixVector_norm]
  by_cases h : ‖matrixVector A‖ = 0
  · erw [if_pos h, h]
    ext p
    simp [matrixVector]
  · erw [if_neg h]
    ext p
    simp [matrixVector, div_eq_mul_inv, mul_comm]

/-- A factored spelling of the literal supplied-order fold step. -/
def orthonormalStep {n q : ℕ} (P : Basis n q) (accepted : List (Square n))
    (j : Fin (q + 1)) : List (Square n) :=
  accepted ++ [normalizeMatrix (fun i k => P j i k -
    ∑ E ∈ accepted.toFinset,
      NLA.Computation.LinearFamilyQuery.inner (P j) E * E i k)]

theorem orthonormalList_eq_fold {n q : ℕ} (P : Basis n q) :
    orthonormalList P = (List.finRange (q + 1)).foldl (orthonormalStep P) [] := rfl

def orderedPrefix {n q : ℕ} (P : Basis n q) (k : ℕ) (hk : k ≤ q + 1) :
    List (Square n) := List.ofFn (fun a : Fin k => orderedMember P (Fin.castLE hk a))

def inputPrefix {q : ℕ} (k : ℕ) (hk : k ≤ q + 1) : List (Fin (q + 1)) :=
  List.ofFn (fun a : Fin k => Fin.castLE hk a)

theorem orderedPrefix_nodup {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (k : ℕ) (hk : k ≤ q + 1) : (orderedPrefix P k hk).Nodup := by
  apply List.nodup_ofFn_ofInjective
  intro a b hab
  apply Fin.ext
  exact congrArg (fun x : Fin (q + 1) => x.val) (orderedMember_injective P hP hab)

/-- No term is lost by the literal `toFinset`: independence makes the
accepted prefix injective, and the earlier indices are exactly `Iio j`. -/
theorem sum_orderedPrefix {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (j : Fin (q + 1)) (F : Square n → ℝ) :
    ∑ E ∈ (orderedPrefix P j.val (Nat.le_of_lt j.isLt)).toFinset, F E =
      ∑ a ∈ Finset.Iio j, F (orderedMember P a) := by
  rw [List.sum_toFinset F (orderedPrefix_nodup P hP _ _)]
  simp only [orderedPrefix, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_bij (fun a _ => Fin.castLE (Nat.le_of_lt j.isLt) a)
  · intro a _
    exact Finset.mem_Iio.mpr a.isLt
  · intro a _ b _ hab
    exact Fin.ext (congrArg (fun x : Fin (q + 1) => x.val) hab)
  · intro b hb
    have hb' : b < j := Finset.mem_Iio.mp hb
    refine ⟨⟨b.val, hb'⟩, Finset.mem_univ _, ?_⟩
    exact Fin.ext rfl
  · intro a _
    rfl

theorem orthonormalStep_orderedPrefix {n q : ℕ} (P : Basis n q)
    (hP : Independent P) (j : Fin (q + 1)) :
    orthonormalStep P (orderedPrefix P j.val (Nat.le_of_lt j.isLt)) j =
      orderedPrefix P j.val (Nat.le_of_lt j.isLt) ++ [orderedMember P j] := by
  have hnorm : normalizeMatrix (fun i k => P j i k -
      ∑ E ∈ (orderedPrefix P j.val (Nat.le_of_lt j.isLt)).toFinset,
        NLA.Computation.LinearFamilyQuery.inner (P j) E * E i k) = orderedMember P j := by
    apply matrixVector_injective
    erw [matrixVector_normalize]
    have hres : matrixVector (fun i k => P j i k -
      ∑ E ∈ (orderedPrefix P j.val (Nat.le_of_lt j.isLt)).toFinset,
        NLA.Computation.LinearFamilyQuery.inner (P j) E * E i k) =
      InnerProductSpace.gramSchmidt ℝ (fun a => matrixVector (P a)) j := by
      rw [ordered_residual]
      congr 1
      funext i k
      rw [sum_orderedPrefix P hP j]
    rw [hres]
    simp [orderedMember, InnerProductSpace.gramSchmidtNormed]
  exact congrArg (fun E => orderedPrefix P j.val (Nat.le_of_lt j.isLt) ++ [E]) hnorm

theorem inputPrefix_succ {q k : ℕ} (hk : k + 1 ≤ q + 1) :
    inputPrefix (q := q) (k + 1) hk =
      inputPrefix k (by omega) ++ [⟨k, by omega⟩] := by
  unfold inputPrefix
  rw [List.ofFn_succ_last]
  rfl

theorem orderedPrefix_succ {n q k : ℕ} (P : Basis n q) (hk : k + 1 ≤ q + 1) :
    orderedPrefix P (k + 1) hk =
      orderedPrefix P k (by omega) ++ [orderedMember P ⟨k, by omega⟩] := by
  unfold orderedPrefix
  rw [List.ofFn_succ_last]
  rfl

/-- Exact equality of every actual finite fold prefix with the fixed-order
normalized Gram--Schmidt coordinates; no replacement basis is selected. -/
theorem orthonormal_fold_prefix {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (k : ℕ) (hk : k ≤ q + 1) :
    (inputPrefix (q := q) k hk).foldl (orthonormalStep P) [] =
      orderedPrefix P k hk := by
  induction k with
  | zero => simp [inputPrefix, orderedPrefix]
  | succ k ih =>
    rw [inputPrefix_succ, List.foldl_append, ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [orthonormalStep_orderedPrefix P hP ⟨k, by omega⟩, orderedPrefix_succ]

theorem orthonormalList_eq_orderedPrefix {n q : ℕ} (P : Basis n q)
    (hP : Independent P) :
    orthonormalList P = orderedPrefix P (q + 1) le_rfl := by
  rw [orthonormalList_eq_fold]
  have hi : inputPrefix (q := q) (q + 1) le_rfl = List.finRange (q + 1) := by
    simp [inputPrefix, List.finRange]
  rw [← hi]
  exact orthonormal_fold_prefix P hP _ _

end NLA.Proofs.RE05
