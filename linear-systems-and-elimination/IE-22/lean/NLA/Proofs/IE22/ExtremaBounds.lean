import NLA.Proofs.IE22.EnergyBounds

/-! The actual matrix supremum has nonempty bounded values on positive
dimensions. Square-root transport uses the literal energy infimum. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open Set
namespace NLA.Proofs.IE22
open NLA.Statements.RowDeletion NLA.Statements.IE22

def normalizedSubsingular {m n : ℕ} (θ : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt ((n : ℝ) / (m : ℝ)) * Real.sqrt (SubsingularSquared θ A)

theorem normalizedSubsingular_nonneg {m n : ℕ} (θ : ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ normalizedSubsingular θ A := by
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem normalizedSubsingular_sq {θ : ℝ} {m n : ℕ}
    (hθ : θ ≤ 1) (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) :
    (normalizedSubsingular θ A) ^ 2 = (n : ℝ) / (m : ℝ) * SubsingularSquared θ A := by
  unfold normalizedSubsingular
  rw [mul_pow, Real.sq_sqrt (div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg m)),
    Real.sq_sqrt (subsingularSquared_nonneg hθ hn A)]

theorem unitRows_entry_sq_le_one {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : UnitRows A) (i : Fin m) (j : Fin n) : A i j ^ 2 ≤ 1 := by
  calc
    _ ≤ ∑ k : Fin n, A i k ^ 2 := Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    _ = 1 := hA i

theorem subsingularSquared_le_rowCount {θ : ℝ} {m n : ℕ}
    (hθ : θ ≤ 1) (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) (hA : UnitRows A) :
    SubsingularSquared θ A ≤ (m : ℝ) := by
  classical
  obtain ⟨S, hS⟩ := exists_retained_rows (m := m) hθ
  let j₀ : Fin n := ⟨0, hn⟩
  let x : Fin n → ℝ := fun j => if j = j₀ then 1 else 0
  have hx : UnitVector x := by simp [UnitVector, x]
  have hrow (i : Fin m) : RowValue A i x = A i j₀ := by simp [RowValue, x]
  calc
    _ ≤ ∑ i ∈ S, (RowValue A i x) ^ 2 := subsingularSquared_le_energy A S hS x hx
    _ = ∑ i ∈ S, A i j₀ ^ 2 := by simp_rw [hrow]
    _ ≤ ∑ _i ∈ S, (1 : ℝ) := Finset.sum_le_sum (fun i _ => unitRows_entry_sq_le_one A hA i j₀)
    _ = (S.card : ℝ) := by simp
    _ ≤ (m : ℝ) := by exact_mod_cast (hS ▸ retainedCount_le hθ m)

theorem normalizedSubsingular_le_sqrt_dimension {θ : ℝ} {m n : ℕ}
    (hθ : θ ≤ 1) (hn : 0 < n) (hm : 0 < m)
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : UnitRows A) :
    normalizedSubsingular θ A ≤ Real.sqrt (n : ℝ) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  apply (sq_le_sq₀ (normalizedSubsingular_nonneg θ A) (Real.sqrt_nonneg _)).1
  rw [normalizedSubsingular_sq hθ hn, Real.sq_sqrt (Nat.cast_nonneg n)]
  calc
    _ ≤ ((n : ℝ) / (m : ℝ)) * (m : ℝ) :=
      mul_le_mul_of_nonneg_left (subsingularSquared_le_rowCount hθ hn A hA)
        (div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg m))
    _ = _ := div_mul_cancel₀ _ hmR

theorem extremum_values_nonempty {θ : ℝ} {m n : ℕ} (hn : 0 < n) :
    {y : ℝ | ∃ A : Matrix (Fin m) (Fin n) ℝ, UnitRows A ∧
      y = Real.sqrt ((n : ℝ) / (m : ℝ)) * Real.sqrt (SubsingularSquared θ A)}.Nonempty := by
  obtain ⟨x, hx⟩ := exists_unit_vector hn
  exact ⟨_, (fun _ => x), (fun _ => hx), rfl⟩

theorem extremum_values_bddAbove {θ : ℝ} {m n : ℕ}
    (hθ : θ ≤ 1) (hn : 0 < n) (hm : 0 < m) :
    BddAbove {y : ℝ | ∃ A : Matrix (Fin m) (Fin n) ℝ, UnitRows A ∧
      y = Real.sqrt ((n : ℝ) / (m : ℝ)) * Real.sqrt (SubsingularSquared θ A)} := by
  refine ⟨Real.sqrt (n : ℝ), ?_⟩
  rintro y ⟨A, hA, rfl⟩
  exact normalizedSubsingular_le_sqrt_dimension hθ hn hm A hA

theorem normalizedSubsingular_le_extremum {θ : ℝ} {m n : ℕ}
    (hθ : θ ≤ 1) (hn : 0 < n) (hm : 0 < m)
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : UnitRows A) :
    normalizedSubsingular θ A ≤ Extremum θ m n := by
  exact le_csSup (extremum_values_bddAbove hθ hn hm) ⟨A, hA, rfl⟩

theorem extremum_nonneg {θ : ℝ} {m n : ℕ}
    (hθ : θ ≤ 1) (hn : 0 < n) (hm : 0 < m) : 0 ≤ Extremum θ m n := by
  obtain ⟨x, hx⟩ := exists_unit_vector hn
  exact (normalizedSubsingular_nonneg θ (fun _ => x)).trans
    (normalizedSubsingular_le_extremum hθ hn hm (fun _ => x) (fun _ => hx))

theorem extremum_le_of_squared_bound {θ c : ℝ} {m n : ℕ}
    (hθ : θ ≤ 1) (hn : 0 < n) (hc : 0 ≤ c)
    (hbound : ∀ A : Matrix (Fin m) (Fin n) ℝ, UnitRows A →
      (n : ℝ) / (m : ℝ) * SubsingularSquared θ A ≤ c ^ 2) :
    Extremum θ m n ≤ c := by
  apply csSup_le (extremum_values_nonempty hn)
  rintro y ⟨A, hA, rfl⟩
  change normalizedSubsingular θ A ≤ c
  apply (sq_le_sq₀ (normalizedSubsingular_nonneg θ A) hc).1
  rw [normalizedSubsingular_sq hθ hn]
  exact hbound A hA

#assert_trust kernel normalizedSubsingular_sq
#assert_trust kernel subsingularSquared_le_rowCount
#assert_trust kernel normalizedSubsingular_le_sqrt_dimension
#assert_trust kernel extremum_values_nonempty
#assert_trust kernel extremum_values_bddAbove
#assert_trust kernel normalizedSubsingular_le_extremum
#assert_trust kernel extremum_nonneg
#assert_trust kernel extremum_le_of_squared_bound
#print axioms extremum_nonneg
#print axioms extremum_le_of_squared_bound
end NLA.Proofs.IE22
