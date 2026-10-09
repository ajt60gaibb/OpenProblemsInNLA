import NLA.TR07.FinitePaths

/-!
# Markov paths with retained independent inputs

Retaining the reservoir chunks makes the reconstruction-to-actual-columns
bridge explicit. Domination concerns unnormalized masses, with no conditioning
on a favorable sequence of transitions.
-/
noncomputable section
open scoped BigOperators
namespace NLA.TR07.Law

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem bind_pos_witness (p : Law α) (q : α → Law β) (b : β)
    (h : 0 < (p.bind q).wt b) : ∃ a, 0 < p.wt a ∧ 0 < (q a).wt b := by
  obtain ⟨a, _, ha⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun a _ => mul_nonneg (p.nonneg a) ((q a).nonneg b))).mp h
  refine ⟨a, ?_, ?_⟩ <;> nlinarith [p.nonneg a, (q a).nonneg b]

theorem map_pos_witness (p : Law α) (f : α → β) (b : β)
    (h : 0 < (p.map f).wt b) : ∃ a, 0 < p.wt a ∧ f a = b := by
  classical
  obtain ⟨a, ha, hb⟩ := bind_pos_witness p (fun a => pure (f a)) b h
  refine ⟨a, ha, ?_⟩
  by_contra he
  simp [pure, Ne.symm he] at hb

theorem expect_mono_on_support (p : Law α) {f g : α → ℝ}
    (h : ∀ a, 0 < p.wt a → f a ≤ g a) : p.expect f ≤ p.expect g := by
  apply Finset.sum_le_sum
  intro a _
  by_cases hz : p.wt a = 0
  · simp [hz]
  · exact mul_le_mul_of_nonneg_left (h a (lt_of_le_of_ne (p.nonneg a) (Ne.symm hz))) (p.nonneg a)

theorem scaled_expect_le (p q : Law α) {c : ℝ}
    (h : ∀ a, c * p.wt a ≤ q.wt a) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    c * p.expect f ≤ q.expect f := by
  simp only [expect, Finset.mul_sum, ← mul_assoc]
  exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (h a) (hf a)

theorem map_scaled (p q : Law α) {c : ℝ}
    (h : ∀ a, c * p.wt a ≤ q.wt a) (f : α → β) (b : β) :
    c * (p.map f).wt b ≤ (q.map f).wt b := by
  classical
  simp only [map, bind, Finset.mul_sum, ← mul_assoc]
  exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (h a) ((pure (f a)).nonneg b)

theorem iid_scaled (p q : Law α) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ a, c * p.wt a ≤ q.wt a) (b : ℕ) (x : Fin b → α) :
    c ^ b * (p.iid b).wt x ≤ (q.iid b).wt x := by
  have hp := Finset.prod_le_prod
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin b))) => mul_nonneg hc (p.nonneg (x i)))
    (fun i _ => h (x i))
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, iid_wt] using hp

theorem iid_map_expect (p : Law α) (g : α → β) (b : ℕ) (f : (Fin b → β) → ℝ) :
    ((p.map g).iid b).expect f = (p.iid b).expect (fun x => f (fun i => g (x i))) := by
  induction b with
  | zero =>
    simp only [expect_iid_zero]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ b ih =>
    rw [expect_iid_succ, expect_iid_succ, expect_map]
    apply p.expect_congr
    intro a
    rw [ih]
    congr 1
    funext x
    congr 1
    ext i
    refine Fin.cases rfl (fun _ => rfl) i

theorem iid_pos_coordinate (p : Law α) {b : ℕ} (x : Fin b → α)
    (h : 0 < (p.iid b).wt x) (i : Fin b) : 0 < p.wt (x i) := by
  by_contra hn
  have hz : p.wt (x i) = 0 := le_antisymm (not_lt.mp hn) (p.nonneg _)
  have he : (p.iid b).wt x = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ i) hz
  linarith

/-- `step` uses a fresh independent input at each transition, while the result
records both all inputs and all post-transition states. -/
def coupledPaths (p : Law β) (step : α → β → Law α) :
    (L : ℕ) → α → Law ((Fin L → β) × (Fin L → α))
  | 0, _ => pure (Fin.elim0, Fin.elim0)
  | L+1, x => p.bind fun z => (step x z).bind fun y =>
      (coupledPaths p step L y).map fun out => (Fin.cons z out.1, Fin.cons y out.2)

theorem coupledPaths_inputs (p : Law β) (step : α → β → Law α) (L : ℕ) (x : α)
    (f : (Fin L → β) → ℝ) :
    (coupledPaths p step L x).expect (fun out => f out.1) = (p.iid L).expect f := by
  induction L generalizing x with
  | zero => simp [coupledPaths, expect_iid_zero]
  | succ L ih =>
    simp only [coupledPaths, expect_bind, expect_map]
    rw [expect_iid_succ]
    apply p.expect_congr
    intro z
    calc
      _ = (step x z).expect (fun _ => (p.iid L).expect (fun zs => f (Fin.cons z zs))) := by
        apply (step x z).expect_congr
        intro y
        exact ih y (fun zs => f (Fin.cons z zs))
      _ = _ := expect_const _ _

theorem coupledPaths_states (p : Law β) (step : α → β → Law α) (L : ℕ) (x : α)
    (f : (Fin L → α) → ℝ) :
    (coupledPaths p step L x).expect (fun out => f out.2) =
      (paths (fun x => p.bind (step x)) L x).expect f := by
  induction L generalizing x with
  | zero => simp [coupledPaths, paths]
  | succ L ih =>
    simp only [coupledPaths, expect_bind, expect_map, expect_paths_succ]
    apply p.expect_congr
    intro z
    apply (step x z).expect_congr
    intro y
    exact ih y (fun ys => f (Fin.cons y ys))

theorem paths_scaled_expect_le (K H : α → Law α) {c : ℝ} (hc : 0 ≤ c)
    (hdom : ∀ x y, c * (K x).wt y ≤ (H x).wt y) (L : ℕ) (x : α)
    (f : (Fin L → α) → ℝ) (hf : ∀ z, 0 ≤ f z) :
    c ^ L * (paths K L x).expect f ≤ (paths H L x).expect f := by
  induction L generalizing x with
  | zero => simp [paths]
  | succ L ih =>
    rw [expect_paths_succ, expect_paths_succ]
    calc
      c ^ (L + 1) * (K x).expect (fun y => (paths K L y).expect (fun z => f (Fin.cons y z))) =
          c * (K x).expect (fun y => c ^ L * (paths K L y).expect (fun z => f (Fin.cons y z))) := by
        rw [expect_const_mul, pow_succ]; ring
      _ ≤ (H x).expect (fun y => c ^ L * (paths K L y).expect (fun z => f (Fin.cons y z))) :=
        scaled_expect_le _ _ (hdom x) _ (fun y => mul_nonneg (pow_nonneg hc _) (expect_nonneg _ (fun z => hf _)))
      _ ≤ _ := (H x).expect_mono (fun y => ih y _ (fun z => hf _))

/-- A pointwise property of every visited state, inherited from a one-step
property and retained with the actual input that supplied the state. -/
theorem coupledPaths_local_support (p : Law β) (step : α → β → Law α)
    (R : β → α → Prop) (hstep : ∀ x z y, 0 < (step x z).wt y → R z y)
    (L : ℕ) (x : α) (out : (Fin L → β) × (Fin L → α))
    (h : 0 < (coupledPaths p step L x).wt out) : ∀ j, R (out.1 j) (out.2 j) := by
  induction L generalizing x with
  | zero => intro j; exact Fin.elim0 j
  | succ L ih =>
    obtain ⟨z, _, hz⟩ := bind_pos_witness p _ out h
    obtain ⟨y, hy, hyout⟩ := bind_pos_witness (step x z) _ out hz
    obtain ⟨tail, ht, he⟩ := map_pos_witness _ _ out hyout
    subst out
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · exact hstep x z y hy
    · exact ih y tail ht j

end NLA.TR07.Law
