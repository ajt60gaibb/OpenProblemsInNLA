/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, University of Cambridge.
All column histories, including the penultimate column and the final scalar.
-/
import NLA.IE14.FrontBounds

noncomputable section
namespace NLA.IE14

theorem front_zero_run {n : ℕ} (hn : 4 ≤ n) (A : Mat n) (hA : CyclicInput A)
    (path : PivotPath n) (hp : AdmissiblePath A path) (K : ℕ) (hK : K ≤ n-2)
    (j : Fin n) (hj : K ≤ j.val) (hinit : frontSum hn A path 0 j=0)
    (hzero : ∀ t : ℕ, (ht : t<K) → A ⟨t+1,by omega⟩ j=0) :
    frontMax hn A path K j=0 ∧ frontSum hn A path K j=0 := by
  have hrun : ∀ t : ℕ, t ≤ K →
      frontMax hn A path t j=0 ∧ frontSum hn A path t j=0 := by
    intro t
    induction t with
    | zero =>
      intro ht
      refine ⟨?_,hinit⟩
      apply le_antisymm
      · simpa only [hinit] using frontMax_le_sum hn A path 0 j
      · exact frontMax_nonneg hn A path 0 j
    | succ t ih =>
      intro ht
      have hi := ih (by omega)
      have hs := front_zero_step hn A hA path hp t (by omega) j (by omega)
        (hzero t (by omega))
      simp only [hi.1, hi.2, add_zero] at hs
      exact ⟨le_antisymm hs.1 (frontMax_nonneg hn A path (t+1) j),
        le_antisymm hs.2 (frontSum_nonneg hn A path (t+1) j)⟩
  exact hrun K le_rfl

theorem front_fibonacci_run {n : ℕ} (hn : 4 ≤ n) (A : Mat n) (hA : CyclicInput A)
    (path : PivotPath n) (hp : AdmissiblePath A path) (K : ℕ) (hK : K ≤ n-2)
    (j : Fin n) (hj : K ≤ j.val) (d : ℕ)
    (hm : frontMax hn A path 0 j ≤ (Nat.fib d : ℝ)*entryMax A)
    (hs : frontSum hn A path 0 j ≤ (Nat.fib (d+1) : ℝ)*entryMax A)
    (hzero : ∀ t : ℕ, (ht : t<K) → A ⟨t+1,by omega⟩ j=0) :
    frontMax hn A path K j ≤ (Nat.fib (d+K) : ℝ)*entryMax A ∧
    frontSum hn A path K j ≤ (Nat.fib (d+K+1) : ℝ)*entryMax A := by
  have hrun : ∀ t : ℕ, t ≤ K →
      frontMax hn A path t j ≤ (Nat.fib (d+t) : ℝ)*entryMax A ∧
      frontSum hn A path t j ≤ (Nat.fib (d+t+1) : ℝ)*entryMax A := by
    intro t
    induction t with
    | zero => intro ht; simpa only [Nat.add_zero] using And.intro hm hs
    | succ t ih =>
      intro ht
      have hi := ih (by omega)
      have hz := front_zero_step hn A hA path hp t (by omega) j (by omega)
        (hzero t (by omega))
      constructor
      · simpa only [Nat.add_assoc] using hz.1.trans hi.2
      · calc
          _ ≤ frontSum hn A path t j+frontMax hn A path t j := hz.2
          _ ≤ (Nat.fib (d+t+1):ℝ)*entryMax A+(Nat.fib (d+t):ℝ)*entryMax A :=
            add_le_add hi.2 hi.1
          _ = (Nat.fib (d+(t+1)+1):ℝ)*entryMax A := by
            rw [show d+(t+1)+1=d+t+2 by omega, Nat.fib_add_two, Nat.cast_add]
            ring
  exact hrun K le_rfl

theorem front_initial_max_le {n : ℕ} (hn : 4 ≤ n) (A : Mat n) (path : PivotPath n)
    (j : Fin n) : frontMax hn A path 0 j ≤ entryMax A := by
  exact max_le (norm_le_entryMax A _ _) (norm_le_entryMax A _ _)

theorem front_initial_sum_le {n : ℕ} (hn : 4 ≤ n) (A : Mat n) (path : PivotPath n)
    (j : Fin n) : frontSum hn A path 0 j ≤ 2*entryMax A := by
  have h0 := norm_le_entryMax A (⟨0,by omega⟩ : Fin n) j
  have hlast := norm_le_entryMax A (⟨n-1,by omega⟩ : Fin n) j
  change ‖A ⟨0,by omega⟩ j‖+‖A ⟨n-1,by omega⟩ j‖ ≤ 2*entryMax A
  linarith

theorem last_column_run {n : ℕ} (hn : 4 ≤ n) (A : Mat n) (hA : CyclicInput A)
    (path : PivotPath n) (hp : AdmissiblePath A path) (j : Fin n) (hj : j.val=n-1)
    (K : ℕ) (hK : K ≤ n-3) :
    frontMax hn A path K j ≤ (Nat.fib (K+2):ℝ)*entryMax A ∧
    frontSum hn A path K j ≤ (Nat.fib (K+3):ℝ)*entryMax A := by
  have hm : frontMax hn A path 0 j ≤ (Nat.fib 2:ℝ)*entryMax A := by
    simpa using front_initial_max_le hn A path j
  have hs : frontSum hn A path 0 j ≤ (Nat.fib (2+1):ℝ)*entryMax A := by
    simpa [Nat.fib_add_two] using front_initial_sum_le hn A path j
  have hz : ∀ t : ℕ, (ht : t<K) → A ⟨t+1,by omega⟩ j=0 := by
    intro t ht
    apply hA.2.1
    simp only [CyclicPosition]
    omega
  have h := front_fibonacci_run hn A hA path hp K (by omega) j (by omega) 2 hm hs hz
  simpa only [show 2+K=K+2 by omega, show K+2+1=K+3 by omega] using h

theorem last_column_sum_bound {n : ℕ} (hn : 4 ≤ n) (A : Mat n) (hA : CyclicInput A)
    (path : PivotPath n) (hp : AdmissiblePath A path) (j : Fin n) (hj : j.val=n-1) :
    frontSum hn A path (n-2) j ≤ fibonacciBound n*entryMax A := by
  have hr := last_column_run hn A hA path hp j hj (n-3) le_rfl
  rw [show n-3+2=n-1 by omega, show n-3+3=n by omega] at hr
  have hs := front_step_bounds hn A hA path hp (n-3) (by omega) j (by omega)
    (entryMax A) (norm_le_entryMax A _ j)
  rw [show n-3+1=n-2 by omega] at hs
  have hf : (1:ℝ) ≤ (Nat.fib (n-1):ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.fib_pos.mpr (show 0<n-1 by omega)))
  have he : entryMax A ≤ (Nat.fib (n-1):ℝ)*entryMax A := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hf (entryMax_nonneg A)
  have hm := max_le hr.1 he
  calc
    _ ≤ frontSum hn A path (n-3) j+entryMax A+
        max (frontMax hn A path (n-3) j) (entryMax A) := hs.2
    _ ≤ (Nat.fib n:ℝ)*entryMax A+entryMax A+(Nat.fib (n-1):ℝ)*entryMax A :=
      add_le_add (add_le_add hr.2 le_rfl) hm
    _ = fibonacciBound n*entryMax A := by
      have hfib : Nat.fib (n+1)=Nat.fib (n-1)+Nat.fib n := by
        have h := Nat.fib_add_two (n:=n-1)
        rw [show n-1+2=n+1 by omega, show n-1+1=n by omega] at h
        exact h
      rw [fibonacciBound, hfib, Nat.cast_add]
      ring

theorem last_column_front_bound {n : ℕ} (hn : 4 ≤ n) (A : Mat n) (hA : CyclicInput A)
    (path : PivotPath n) (hp : AdmissiblePath A path) (j : Fin n) (hj : j.val=n-1)
    (K : ℕ) (hK : K ≤ n-2) :
    frontMax hn A path K j ≤ fibonacciBound n*entryMax A := by
  by_cases hk : K ≤ n-3
  · have hr := (last_column_run hn A hA path hp j hj K hk).1
    have hf : (Nat.fib (K+2):ℝ) ≤ fibonacciBound n := by
      have h : (Nat.fib (K+2):ℝ) ≤ (Nat.fib (n+1):ℝ) := by
        exact_mod_cast (Nat.fib_mono (show K+2 ≤ n+1 by omega))
      unfold fibonacciBound; linarith
    exact hr.trans (mul_le_mul_of_nonneg_right hf (entryMax_nonneg A))
  · have he : K=n-2 := by omega
    subst K
    exact (frontMax_le_sum hn A path (n-2) j).trans (last_column_sum_bound hn A hA path hp j hj)

theorem penultimate_column_run {n : ℕ} (hn : 4 ≤ n) (A : Mat n) (hA : CyclicInput A)
    (path : PivotPath n) (hp : AdmissiblePath A path) (j : Fin n) (hj : j.val=n-2)
    (K : ℕ) (hK : K ≤ n-4) :
    frontMax hn A path K j ≤ (Nat.fib (K+1):ℝ)*entryMax A ∧
    frontSum hn A path K j ≤ (Nat.fib (K+2):ℝ)*entryMax A := by
  have hfirst : A (⟨0,by omega⟩ : Fin n) j=0 := by
    apply hA.2.1
    simp only [CyclicPosition]
    omega
  have hm : frontMax hn A path 0 j ≤ (Nat.fib 1:ℝ)*entryMax A := by
    simpa using front_initial_max_le hn A path j
  have hs : frontSum hn A path 0 j ≤ (Nat.fib (1+1):ℝ)*entryMax A := by
    simpa [frontSum, frontPair, trajectory, hfirst] using norm_le_entryMax A ⟨n-1,by omega⟩ j
  have hz : ∀ t : ℕ, (ht : t<K) → A ⟨t+1,by omega⟩ j=0 := by
    intro t ht
    apply hA.2.1
    simp only [CyclicPosition]
    omega
  have h := front_fibonacci_run hn A hA path hp K (by omega) j (by omega) 1 hm hs hz
  simpa only [show 1+K=K+1 by omega, show K+1+1=K+2 by omega] using h

theorem penultimate_column_transition {n : ℕ} (hn : 4 ≤ n) (A : Mat n) (hA : CyclicInput A)
    (path : PivotPath n) (hp : AdmissiblePath A path) (j : Fin n) (hj : j.val=n-2) :
    frontMax hn A path (n-3) j ≤ 2*(Nat.fib (n-3):ℝ)*entryMax A ∧
    frontSum hn A path (n-3) j ≤ ((Nat.fib (n-1):ℝ)+1)*entryMax A := by
  have hr := penultimate_column_run hn A hA path hp j hj (n-4) le_rfl
  rw [show n-4+1=n-3 by omega, show n-4+2=n-2 by omega] at hr
  have hs := front_step_bounds hn A hA path hp (n-4) (by omega) j (by omega)
    (entryMax A) (norm_le_entryMax A _ j)
  rw [show n-4+1=n-3 by omega] at hs
  have hE := entryMax_nonneg A
  have hf : (1:ℝ) ≤ (Nat.fib (n-3):ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.fib_pos.mpr (show 0<n-3 by omega)))
  have he : entryMax A ≤ (Nat.fib (n-3):ℝ)*entryMax A := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hf hE
  have hrec₁ : Nat.fib (n-1)=Nat.fib (n-3)+Nat.fib (n-2) := by
    have h := Nat.fib_add_two (n:=n-3)
    rw [show n-3+2=n-1 by omega, show n-3+1=n-2 by omega] at h
    exact h
  have hrec₂ : Nat.fib (n-2)=Nat.fib (n-4)+Nat.fib (n-3) := by
    have h := Nat.fib_add_two (n:=n-4)
    rw [show n-4+2=n-2 by omega, show n-4+1=n-3 by omega] at h
    exact h
  have hdouble : (Nat.fib (n-2):ℝ) ≤ 2*(Nat.fib (n-3):ℝ) := by
    have hm := Nat.fib_mono (show n-4 ≤ n-3 by omega)
    have hi : Nat.fib (n-2) ≤ 2*Nat.fib (n-3) := by omega
    exact_mod_cast hi
  constructor
  · apply hs.1.trans
    apply max_le
    · exact hr.2.trans (mul_le_mul_of_nonneg_right hdouble hE)
    · linarith [hr.1]
  · calc
      _ ≤ frontSum hn A path (n-4) j+entryMax A+
          max (frontMax hn A path (n-4) j) (entryMax A) := hs.2
      _ ≤ (Nat.fib (n-2):ℝ)*entryMax A+entryMax A+(Nat.fib (n-3):ℝ)*entryMax A :=
        add_le_add (add_le_add hr.2 le_rfl) (max_le hr.1 he)
      _ = ((Nat.fib (n-1):ℝ)+1)*entryMax A := by rw [hrec₁, Nat.cast_add]; ring

theorem penultimate_column_front_bound {n : ℕ} (hn : 4 ≤ n) (A : Mat n) (hA : CyclicInput A)
    (path : PivotPath n) (hp : AdmissiblePath A path) (j : Fin n) (hj : j.val=n-2)
    (K : ℕ) (hK : K ≤ n-2) :
    frontMax hn A path K j ≤ ((Nat.fib (n-1):ℝ)+1)*entryMax A := by
  have hE := entryMax_nonneg A
  have hdouble : 2*(Nat.fib (n-3):ℝ) ≤ (Nat.fib (n-1):ℝ) := by
    have h := Nat.fib_add_two (n:=n-3)
    rw [show n-3+2=n-1 by omega, show n-3+1=n-2 by omega] at h
    have hm := Nat.fib_mono (show n-3 ≤ n-2 by omega)
    have hi : 2*Nat.fib (n-3) ≤ Nat.fib (n-1) := by omega
    exact_mod_cast hi
  by_cases hk : K ≤ n-4
  · have hr := (penultimate_column_run hn A hA path hp j hj K hk).1
    have hf : (Nat.fib (K+1):ℝ) ≤ (Nat.fib (n-1):ℝ)+1 := by
      have h : (Nat.fib (K+1):ℝ) ≤ (Nat.fib (n-1):ℝ) := by
        exact_mod_cast (Nat.fib_mono (show K+1 ≤ n-1 by omega))
      linarith
    exact hr.trans (mul_le_mul_of_nonneg_right hf hE)
  have ht := penultimate_column_transition hn A hA path hp j hj
  by_cases hk' : K=n-3
  · subst K
    apply ht.1.trans
    exact mul_le_mul_of_nonneg_right (by linarith) hE
  · have he : K=n-2 := by omega
    subst K
    have hs := front_step_bounds hn A hA path hp (n-3) (by omega) j (by omega)
      (entryMax A) (norm_le_entryMax A _ j)
    rw [show n-3+1=n-2 by omega] at hs
    apply hs.1.trans
    apply max_le ht.2
    have hd := mul_le_mul_of_nonneg_right hdouble hE
    nlinarith [ht.1]

theorem middle_column_zero_run {n : ℕ} (hn : 4 ≤ n) (A : Mat n) (hA : CyclicInput A)
    (path : PivotPath n) (hp : AdmissiblePath A path) (j : Fin n)
    (hjlo : 2 ≤ j.val) (hjhi : j.val ≤ n-3) (K : ℕ) (hK : K ≤ j.val-2) :
    frontMax hn A path K j=0 ∧ frontSum hn A path K j=0 := by
  have hfirst : A (⟨0,by omega⟩ : Fin n) j=0 := by
    apply hA.2.1; simp only [CyclicPosition]; omega
  have hlast : A (⟨n-1,by omega⟩ : Fin n) j=0 := by
    apply hA.2.1; simp only [CyclicPosition]; omega
  apply front_zero_run hn A hA path hp K (by omega) j (by omega)
  · simp [frontSum, frontPair, trajectory, hfirst, hlast]
  · intro t ht
    apply hA.2.1; simp only [CyclicPosition]; omega

theorem middle_column_front_bound {n : ℕ} (hn : 4 ≤ n) (A : Mat n) (hA : CyclicInput A)
    (path : PivotPath n) (hp : AdmissiblePath A path) (j : Fin n)
    (hjlo : 2 ≤ j.val) (hjhi : j.val ≤ n-3) (K : ℕ) (hK : K ≤ j.val) :
    frontMax hn A path K j ≤ 2*entryMax A := by
  have hE := entryMax_nonneg A
  by_cases hk : K ≤ j.val-2
  · rw [(middle_column_zero_run hn A hA path hp j hjlo hjhi K hk).1]
    positivity
  have hr := middle_column_zero_run hn A hA path hp j hjlo hjhi (j.val-2) le_rfl
  have hs := front_step_bounds hn A hA path hp (j.val-2) (by omega) j (by omega)
    (entryMax A) (norm_le_entryMax A _ j)
  rw [show j.val-2+1=j.val-1 by omega] at hs
  simp only [hr.1, hr.2, zero_add, max_eq_right hE] at hs
  have hs' : frontMax hn A path (j.val-1) j ≤ entryMax A ∧
      frontSum hn A path (j.val-1) j ≤ 2*entryMax A := ⟨hs.1,by linarith [hs.2]⟩
  by_cases hk' : K=j.val-1
  · subst K; linarith [hs'.1]
  · have he : K=j.val := by omega
    subst K
    have ht := front_step_bounds hn A hA path hp (j.val-1) (by omega) j (by omega)
      (entryMax A) (norm_le_entryMax A _ j)
    rw [show j.val-1+1=j.val by omega] at ht
    exact ht.1.trans (max_le hs'.2 (by linarith [hs'.1]))

theorem second_column_front_bound {n : ℕ} (hn : 4 ≤ n) (A : Mat n) (hA : CyclicInput A)
    (path : PivotPath n) (hp : AdmissiblePath A path) (j : Fin n) (hj : j.val=1)
    (K : ℕ) (hK : K ≤ 1) : frontMax hn A path K j ≤ 2*entryMax A := by
  have hE := entryMax_nonneg A
  by_cases hk : K=0
  · subst K; linarith [front_initial_max_le hn A path j]
  have he : K=1 := by omega
  subst K
  have hlast : A (⟨n-1,by omega⟩ : Fin n) j=0 := by
    apply hA.2.1; simp only [CyclicPosition]; omega
  have hsum : frontSum hn A path 0 j ≤ entryMax A := by
    simpa [frontSum, frontPair, trajectory, hlast] using norm_le_entryMax A ⟨0,by omega⟩ j
  have hs := front_step_bounds hn A hA path hp 0 (by omega) j (by omega)
    (entryMax A) (norm_le_entryMax A _ j)
  apply hs.1.trans
  apply max_le
  · linarith
  · linarith [front_initial_max_le hn A path j]

/-- The complete all-complex, all-tie, all-active-entry upper bound. -/
theorem all_active_entries_bound_proved (n : ℕ) (hn : 4 ≤ n) (A : Mat n) (hA : CyclicInput A)
    (path : PivotPath n) (hp : AdmissiblePath A path) :
    ∀ k : Fin n, ∀ i j : Fin n, k ≤ i → k ≤ j →
      ‖trajectory A path k.val i j‖ ≤ fibonacciBound n * entryMax A := by
  intro k i j hi hj
  have hE := entryMax_nonneg A
  have hC : (2:ℝ) ≤ fibonacciBound n := by
    have hf : (1:ℝ) ≤ (Nat.fib (n+1):ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt (Nat.fib_pos.mpr (show 0<n+1 by omega)))
    unfold fibonacciBound; linarith
  have hEbound : entryMax A ≤ fibonacciBound n*entryMax A := by
    have hc : (1:ℝ) ≤ fibonacciBound n := by linarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc hE
  by_cases hk : k.val=n-1
  · have hil : i=(⟨n-1,by omega⟩ : Fin n) := by
      apply Fin.ext; change i.val=n-1
      have hi' : k.val ≤ i.val := hi
      omega
    have hjl : j=(⟨n-1,by omega⟩ : Fin n) := by
      apply Fin.ext; change j.val=n-1
      have hj' : k.val ≤ j.val := hj
      omega
    rw [hk,hil,hjl]
    exact (final_scalar_le_frontSum hn A hA path hp).trans
      (last_column_sum_bound hn A hA path hp _ rfl)
  have hk' : k.val ≤ n-2 := by have := k.isLt; omega
  apply (active_entry_le_front hn A hA path hp k.val hk' i j hi hj).trans
  apply max_le _ hEbound
  by_cases hj0 : j.val=0
  · have hk0 : k.val=0 := by change k.val ≤ j.val at hj; omega
    rw [hk0]
    exact (front_initial_max_le hn A path j).trans hEbound
  by_cases hj1 : j.val=1
  · exact (second_column_front_bound hn A hA path hp j hj1 k.val
      (by change k.val ≤ j.val at hj; omega)).trans (mul_le_mul_of_nonneg_right hC hE)
  by_cases hjlast : j.val=n-1
  · exact last_column_front_bound hn A hA path hp j hjlast k.val hk'
  by_cases hjpen : j.val=n-2
  · have hf : (Nat.fib (n-1):ℝ)+1 ≤ fibonacciBound n := by
      have h : (Nat.fib (n-1):ℝ) ≤ (Nat.fib (n+1):ℝ) := by
        exact_mod_cast (Nat.fib_mono (show n-1 ≤ n+1 by omega))
      exact add_le_add h le_rfl
    exact (penultimate_column_front_bound hn A hA path hp j hjpen k.val hk').trans
      (mul_le_mul_of_nonneg_right hf hE)
  have hjlo : 2 ≤ j.val := by omega
  have hjhi : j.val ≤ n-3 := by have := j.isLt; omega
  exact (middle_column_front_bound hn A hA path hp j hjlo hjhi k.val hj).trans
    (mul_le_mul_of_nonneg_right hC hE)

#assert_trust kernel front_fibonacci_run
#print axioms front_fibonacci_run
#assert_trust kernel last_column_sum_bound
#print axioms last_column_sum_bound
#assert_trust kernel penultimate_column_front_bound
#print axioms penultimate_column_front_bound
#assert_trust kernel all_active_entries_bound_proved
#print axioms all_active_entries_bound_proved

end NLA.IE14
