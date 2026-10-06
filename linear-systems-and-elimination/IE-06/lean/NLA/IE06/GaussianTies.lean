/-
Gaussian pivot ties are null for the exact all-path IE-06 model.
This new common-denominator polynomial proof follows the independently reviewed
plan in reviews/gaussian-ties-specification.md. It uses the attributed generic
polynomial-null theorem from GaussianNull, without stochastic assumptions.
-/
import NLA.IE06.GaussianNull
import NLA.IE06.GEPP

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory

namespace NLA.IE06.GaussianTies

abbrev Poly (n : ℕ) := MvPolynomial (Fin (n * n)) ℝ

def ActivePrefix {n : ℕ} (path : PivotPath n) (k : ℕ) : Prop :=
  ∀ r : Fin n, r.val < k → r ≤ path r

def NonzeroPrefix {n : ℕ} (A : Mat n) (path : PivotPath n) (k : ℕ) : Prop :=
  ∀ r : Fin n, r.val < k → trajectory A path r.val (path r) r ≠ 0

def Supported {n : ℕ} (S : Mat n) (k : ℕ) : Prop :=
  ∀ i j : Fin n, i.val < k ∨ j.val < k → S i j = 0

/-- A polynomial numerator matrix with a common denominator. -/
def symbolicState {n : ℕ} (path : PivotPath n) :
    ℕ → Poly n × Matrix (Fin n) (Fin n) (Poly n)
  | 0 => (1, fun i j => MvPolynomial.X (finProdFinEquiv (i, j)))
  | k + 1 => if h : k < n then
      let r : Fin n := ⟨k, h⟩
      let prev := symbolicState path k
      let P := prev.2 (path r) r
      (prev.1 * P, fun i j => if r < i ∧ r < j then
        prev.2 (Equiv.swap r (path r) i) j * P -
          prev.2 (Equiv.swap r (path r) i) r * prev.2 (path r) j else 0)
    else (1, 0)

theorem symbolicState_eval {n : ℕ} (A : Mat n) (path : PivotPath n)
    (k : ℕ) (hk : k ≤ n) (hnz : NonzeroPrefix A path k) :
    MvPolynomial.eval (GaussianNull.vectorize A) (symbolicState path k).1 ≠ 0 ∧
      ∀ i j, trajectory A path k i j =
        MvPolynomial.eval (GaussianNull.vectorize A) ((symbolicState path k).2 i j) /
          MvPolynomial.eval (GaussianNull.vectorize A) (symbolicState path k).1 := by
  induction k with
  | zero =>
      constructor
      · simp [symbolicState]
      · intro i j
        simp [trajectory, symbolicState, GaussianNull.vectorize]
  | succ k ih =>
      have hkn : k < n := by omega
      let r : Fin n := ⟨k, hkn⟩
      have hprev : NonzeroPrefix A path k := fun s hs => hnz s (by omega)
      obtain ⟨hD, hN⟩ := ih (by omega) hprev
      have hP : MvPolynomial.eval (GaussianNull.vectorize A)
          ((symbolicState path k).2 (path r) r) ≠ 0 := by
        intro hz
        apply hnz r (by dsimp [r]; omega)
        change trajectory A path k (path r) r = 0
        rw [hN, hz, zero_div]
      constructor
      · simpa only [symbolicState, dif_pos hkn, map_mul] using mul_ne_zero hD hP
      · intro i j
        have hstep : trajectory A path (k + 1) =
            schurStep (trajectory A path k) r (path r) := by
          simp only [trajectory, dif_pos hkn, r]
        rw [hstep]
        by_cases hij : r < i ∧ r < j
        · dsimp only [r] at hij hP
          simp only [schurStep, rowSwap, symbolicState, dif_pos hkn, r,
            hij, and_self, if_true, map_sub, map_mul, Equiv.swap_apply_left]
          rw [hN, hN, hN, hN]
          field_simp [hD, hP]
        · dsimp only [r] at hij
          simp only [schurStep, rowSwap, symbolicState, dif_pos hkn, r,
            hij, if_false, map_zero, zero_div]

def liftTail {n : ℕ} (S : Mat n) (k p : Fin n) : Mat n :=
  rowSwap (fun i j => if i = k ∧ j = k then 1 else S i j) k p

theorem liftTail_pivot {n : ℕ} (S : Mat n) (k p : Fin n) :
    liftTail S k p p k = 1 := by
  simp [liftTail, rowSwap]

theorem liftTail_supported {n : ℕ} (S : Mat n) (k p : Fin n)
    (hp : k ≤ p) (hS : Supported S (k.val + 1)) : Supported (liftTail S k p) k.val := by
  intro i j hij
  rcases hij with hi | hj
  · have hik : i ≠ k := by intro h; subst i; omega
    have hip : i ≠ p := by intro h; subst i; omega
    have hz := hS i j (Or.inl (by omega))
    simp [liftTail, rowSwap, Equiv.swap_apply_of_ne_of_ne hik hip, hik, hz]
  · have hjk : j ≠ k := by intro h; subst j; omega
    have hz := hS (Equiv.swap k p i) j (Or.inr (by omega))
    simp [liftTail, rowSwap, hjk, hz]

theorem schurStep_liftTail {n : ℕ} (S : Mat n) (k p : Fin n)
    (hS : Supported S (k.val + 1)) : schurStep (liftTail S k p) k p = S := by
  ext i j
  by_cases hij : k < i ∧ k < j
  · have hik : i ≠ k := ne_of_gt hij.1
    have hjk : j ≠ k := ne_of_gt hij.2
    have hz := hS i k (Or.inr (Nat.lt_succ_self _))
    simp [schurStep, liftTail, rowSwap, hij, hik, hjk, hz]
  · have hz : S i j = 0 := hS i j (by
      by_cases hi : k < i
      · right; have hj : ¬k < j := fun hj => hij ⟨hi, hj⟩; omega
      · left; omega)
    simp [schurStep, hij, hz]

/-- Every supported tail can be realized with the specified active prefix,
even when the requested tail itself is singular. -/
theorem exists_prefix_realizer {n : ℕ} (path : PivotPath n) (k : ℕ)
    (hk : k ≤ n) (hp : ActivePrefix path k) (S : Mat n) (hS : Supported S k) :
    ∃ A : Mat n, trajectory A path k = S ∧ NonzeroPrefix A path k := by
  induction k generalizing S with
  | zero =>
      exact ⟨S, rfl, fun r hr => by omega⟩
  | succ k ih =>
      have hkn : k < n := by omega
      let r : Fin n := ⟨k, hkn⟩
      have hp' : ActivePrefix path k := fun s hs => hp s (by omega)
      have hpr : r ≤ path r := hp r (by dsimp [r]; omega)
      have hlift : Supported (liftTail S r (path r)) k :=
        liftTail_supported S r (path r) hpr hS
      obtain ⟨A, hA, hnz⟩ := ih (by omega) hp' (liftTail S r (path r)) hlift
      refine ⟨A, ?_, ?_⟩
      · simpa only [trajectory, dif_pos hkn, hA] using schurStep_liftTail S r (path r) hS
      · intro s hs
        by_cases hsk : s.val < k
        · exact hnz s hsk
        · have hsr : s = r := Fin.ext (by dsimp [r]; omega)
          subst s
          rw [hA, liftTail_pivot]
          exact one_ne_zero

def tiePolynomial {n : ℕ} (path : PivotPath n) (k i j : Fin n) : Poly n :=
  ((symbolicState path k.val).2 i k) ^ 2 - ((symbolicState path k.val).2 j k) ^ 2

theorem tiePolynomial_ne_zero {n : ℕ} (path : PivotPath n) (k i j : Fin n)
    (hp : ActivePrefix path k.val) (hi : k ≤ i) (hj : k ≤ j) (hij : i ≠ j) :
    tiePolynomial path k i j ≠ 0 := by
  let S : Mat n := fun a b => if a = i ∧ b = k then 1 else 0
  have hS : Supported S k.val := by
    intro a b hab
    have hnot : ¬(a = i ∧ b = k) := by
      rintro ⟨rfl, rfl⟩
      rcases hab with h | h <;> omega
    simp [S, hnot]
  obtain ⟨A, hA, hnz⟩ := exists_prefix_realizer path k.val (Nat.le_of_lt k.isLt) hp S hS
  obtain ⟨hD, hN⟩ := symbolicState_eval A path k.val (Nat.le_of_lt k.isLt) hnz
  have hni : MvPolynomial.eval (GaussianNull.vectorize A)
      ((symbolicState path k.val).2 i k) =
      MvPolynomial.eval (GaussianNull.vectorize A) (symbolicState path k.val).1 := by
    have he := (hN i k).symm
    rw [hA] at he
    simp only [S, and_self, if_true] at he
    simpa only [one_mul] using (div_eq_iff hD).mp he
  have hnj : MvPolynomial.eval (GaussianNull.vectorize A)
      ((symbolicState path k.val).2 j k) = 0 := by
    have he := (hN j k).symm
    rw [hA] at he
    simp only [S, Ne.symm hij, false_and, if_false] at he
    simpa only [zero_mul] using (div_eq_iff hD).mp he
  intro hzero
  have he := congrArg (MvPolynomial.eval (GaussianNull.vectorize A)) hzero
  norm_num only [tiePolynomial, map_sub, map_pow, map_zero, hni, hnj] at he
  exact pow_ne_zero 2 hD (by simpa only [sub_zero] using he)

theorem tie_implies_polynomial_zero {n : ℕ} (A : Mat n) (path : PivotPath n)
    (k i j : Fin n) (hnz : NonzeroPrefix A path k.val)
    (htie : |trajectory A path k.val i k| = |trajectory A path k.val j k|) :
    MvPolynomial.eval (GaussianNull.vectorize A) (tiePolynomial path k i j) = 0 := by
  obtain ⟨hD, hN⟩ := symbolicState_eval A path k.val (Nat.le_of_lt k.isLt) hnz
  have hsquares : (trajectory A path k.val i k) ^ 2 = (trajectory A path k.val j k) ^ 2 :=
    (sq_eq_sq_iff_abs_eq_abs _ _).2 htie
  rw [hN, hN] at hsquares
  simp only [div_pow] at hsquares
  have hnumer := (div_left_inj' (pow_ne_zero 2 hD)).mp hsquares
  simpa only [tiePolynomial, map_sub, map_pow, sub_eq_zero] using hnumer

theorem polynomial_ne_zero_gaussian_ae (n : ℕ) (P : Poly n) (hP : P ≠ 0) :
    ∀ᵐ A ∂ gaussianMatrix n, MvPolynomial.eval (GaussianNull.vectorize A) P ≠ 0 := by
  let _ : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hp := GaussianNull.polynomial_ne_zero_ae (n * n) (fun _ => gaussianReal 0 1) P hP
  rw [← GaussianNull.gaussian_vectorize_map n n] at hp
  have hm : Measurable (@GaussianNull.vectorize n n) := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply _).comp (measurable_pi_apply _)
  exact ae_of_ae_map hm.aemeasurable hp

def ColumnsSeparated {n : ℕ} (A : Mat n) : Prop :=
  ∀ path : PivotPath n, AdmissiblePath A path → ∀ k i j : Fin n,
    k ≤ i → k ≤ j → i ≠ j →
      |trajectory A path k.val i k| ≠ |trajectory A path k.val j k|

theorem columnsSeparated_ae (n : ℕ) :
    ∀ᵐ A ∂ gaussianMatrix n, ColumnsSeparated A := by
  have hfixed : ∀ (path : PivotPath n) (k i j : Fin n),
      ∀ᵐ A ∂ gaussianMatrix n,
        k ≤ i → k ≤ j → i ≠ j → AdmissiblePath A path →
          |trajectory A path k.val i k| ≠ |trajectory A path k.val j k| := by
    intro path k i j
    by_cases hact : ActivePrefix path k.val
    · by_cases hindices : k ≤ i ∧ k ≤ j ∧ i ≠ j
      · have hp := polynomial_ne_zero_gaussian_ae n (tiePolynomial path k i j)
          (tiePolynomial_ne_zero path k i j hact hindices.1 hindices.2.1 hindices.2.2)
        filter_upwards [hp] with A hA
        intro _hi _hj _hne hpath htie
        exact hA (tie_implies_polynomial_zero A path k i j
          (fun r _ => (hpath r).2.1) htie)
      · exact ae_of_all _ fun _ hi hj hne _ => False.elim (hindices ⟨hi, hj, hne⟩)
    · exact ae_of_all _ fun _ _ _ _ hpath =>
        False.elim (hact (fun r _ => (hpath r).1))
  have hall : ∀ᵐ A ∂ gaussianMatrix n, ∀ (path : PivotPath n) (k i j : Fin n),
      k ≤ i → k ≤ j → i ≠ j → AdmissiblePath A path →
        |trajectory A path k.val i k| ≠ |trajectory A path k.val j k| := by
    simpa only [ae_all_iff] using hfixed
  filter_upwards [hall] with A hA
  intro path hpath k i j hi hj hij
  exact hA path k i j hi hj hij hpath

theorem admissiblePath_unique_of_columnsSeparated {n : ℕ} (A : Mat n)
    (hsep : ColumnsSeparated A) (p q : PivotPath n)
    (hp : AdmissiblePath A p) (hq : AdmissiblePath A q) : p = q := by
  have hpivot (k : Fin n) (hstate : trajectory A p k.val = trajectory A q k.val) :
      p k = q k := by
    have hpk := hp k
    have hqk := hq k
    rw [← hstate] at hqk
    by_contra hne
    apply hsep p hp k (p k) (q k) hpk.1 hqk.1 hne
    exact le_antisymm (hqk.2.2 _ hpk.1) (hpk.2.2 _ hqk.1)
  have hstates : ∀ k : ℕ, trajectory A p k = trajectory A q k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        by_cases hk : k < n
        · have he := hpivot ⟨k, hk⟩ ih
          simp only [trajectory, dif_pos hk, ih, he]
        · simp only [trajectory, dif_neg hk]
  funext k
  exact hpivot k (hstates k.val)

#assert_trust kernel symbolicState_eval
#assert_trust kernel liftTail_pivot
#assert_trust kernel liftTail_supported
#assert_trust kernel schurStep_liftTail
#assert_trust kernel exists_prefix_realizer
#assert_trust kernel tiePolynomial_ne_zero
#assert_trust kernel tie_implies_polynomial_zero
#assert_trust kernel polynomial_ne_zero_gaussian_ae
#assert_trust kernel columnsSeparated_ae
#assert_trust kernel admissiblePath_unique_of_columnsSeparated
#print axioms symbolicState_eval
#print axioms liftTail_pivot
#print axioms liftTail_supported
#print axioms schurStep_liftTail
#print axioms exists_prefix_realizer
#print axioms tiePolynomial_ne_zero
#print axioms tie_implies_polynomial_zero
#print axioms polynomial_ne_zero_gaussian_ae
#print axioms columnsSeparated_ae
#print axioms admissiblePath_unique_of_columnsSeparated

end NLA.IE06.GaussianTies

namespace NLA.IE06

/-- All admissible tie paths coincide almost surely under the actual Gaussian
matrix law; existence is supplied by nonsingularity and exact GEPP. -/
theorem gaussianMatrix_admissiblePath_unique_ae (n : ℕ) :
    ∀ᵐ A ∂ gaussianMatrix n, ∃! path : PivotPath n, AdmissiblePath A path := by
  have hnonzero : ∀ᵐ A ∂ gaussianMatrix n, A.det ≠ 0 := by
    simpa only [ae_iff, not_not] using gaussianMatrix_singular_null_proved n
  filter_upwards [GaussianTies.columnsSeparated_ae n, hnonzero] with A hsep hA
  obtain ⟨path, hpath⟩ := admissiblePath_exists_proved A hA
  exact ⟨path, hpath, fun other hother =>
    GaussianTies.admissiblePath_unique_of_columnsSeparated A hsep other path hother hpath⟩

/-- The source's deterministic least-current-index rule agrees almost surely
with every admissible path in the original all-path event. -/
theorem gaussianMatrix_admissiblePath_eq_firstPath_ae (n : ℕ) :
    ∀ᵐ A ∂ gaussianMatrix n, ∀ path : PivotPath n,
      AdmissiblePath A path → path = firstPath A := by
  have hnonzero : ∀ᵐ A ∂ gaussianMatrix n, A.det ≠ 0 := by
    simpa only [ae_iff, not_not] using gaussianMatrix_singular_null_proved n
  filter_upwards [GaussianTies.columnsSeparated_ae n, hnonzero] with A hsep hA
  intro path hpath
  exact GaussianTies.admissiblePath_unique_of_columnsSeparated A hsep path (firstPath A)
    hpath (firstPath_admissible_proved A hA)

#assert_trust kernel gaussianMatrix_admissiblePath_unique_ae
#assert_trust kernel gaussianMatrix_admissiblePath_eq_firstPath_ae
#print axioms gaussianMatrix_admissiblePath_unique_ae
#print axioms gaussianMatrix_admissiblePath_eq_firstPath_ae

end NLA.IE06
