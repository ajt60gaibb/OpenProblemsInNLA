import ProofProject.ReplicationBound
import ProofProject.ReplicatedSpace
import ProofProject.FiniteModelLower

/-!
# Finite sign models from coefficient replication

The copied unit family is ordered consecutively, with numerical coordinate
`i*r+l`. Its elementary patterns are controlled by the deficit theorem, and
constant coefficients within each group preserve the original sign gain.
-/

noncomputable section

open scoped BigOperators

namespace ProofProject

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ}

/-- The concrete replicated family in consecutive numerical order. -/
def replicatedOrderedFamily (f : Fin n → H) (r : ℕ) (k : Fin (n * r)) :
    ReplicatedSpace H n r := replicatedFamily f r (copiedIndexEquiv.symm k)

lemma replicatedOrderedFamily_norm (f : Fin n → H) {r : ℕ} (hr : 0 < r)
    (hf : ∀ i, ‖f i‖ = 1) (k : Fin (n * r)) :
    ‖replicatedOrderedFamily f r k‖ = 1 :=
  replicatedFamily_norm f hr hf _

/-- Consecutive synthesis has exactly the proved replicated energy. -/
lemma replicatedOrderedFamily_synthesis_norm_sq (f : Fin n → H) (r : ℕ)
    (a : Fin (n * r) → ℂ) :
    ‖finiteSynthesis (replicatedOrderedFamily f r) a‖ ^ 2 =
      copiedEnergy f r (copiedCoefficients a) := by
  unfold finiteSynthesis replicatedOrderedFamily
  rw [finiteSynthesis_copiedFamily]
  simpa only [Fintype.sum_prod_type] using replicatedFamily_synthesis_norm_sq f r (copiedCoefficients a)

/-- The constant-group embedding, written in consecutive coordinates. -/
def copiedOrderedLift (r : ℕ) (a : Fin n → ℂ) : Fin (n * r) → ℂ :=
  copiedCoefficients.symm (copiedLift r a)

@[simp] lemma copiedOrderedLift_apply (r : ℕ) (a : Fin n → ℂ) (i : Fin n) (l : Fin r) :
    copiedOrderedLift r a (copiedIndexEquiv (i, l)) = copiedLift r a i l := by
  change copiedCoefficients (copiedCoefficients.symm (copiedLift r a)) i l = _
  rw [LinearEquiv.apply_symm_apply]

lemma copiedOrderedLift_ne_zero {r : ℕ} (hr : 0 < r) {a : Fin n → ℂ} (ha : a ≠ 0) :
    copiedOrderedLift r a ≠ 0 := by
  intro h
  apply copiedLift_ne_zero hr ha
  have he := congrArg copiedCoefficients h
  simpa [copiedOrderedLift] using he

/-- The consecutive constant-group embedding preserves synthesis norms. -/
lemma replicatedOrderedFamily_copiedLift_norm (f : Fin n → H) {r : ℕ}
    (hr : 0 < r) (a : Fin n → ℂ) :
    ‖finiteSynthesis (replicatedOrderedFamily f r) (copiedOrderedLift r a)‖ =
      ‖finiteSynthesis f a‖ := by
  unfold finiteSynthesis replicatedOrderedFamily
  rw [finiteSynthesis_copiedFamily]
  simp only [copiedOrderedLift, LinearEquiv.apply_symm_apply]
  simpa only [Fintype.sum_prod_type, finiteSynthesis] using replicatedFamily_copiedLift_norm f hr a

/-- Replication provides the exact elementary-pattern bound on the actual
copied family, with its consecutive order. -/
theorem replicatedOrderedFamily_pattern_bound (f : Fin n → H) {r : ℕ} (hr : 0 < r)
    {M c C : ℝ} (hM : 1 ≤ M) (hf : ∀ i, ‖f i‖ = 1)
    (hdef : HasReplicationDeficits f M c C) (hbudget : C ≤ ((r : ℝ) - 1) * c)
    (a : Fin (n * r) → ℂ) (k : Fin (n * r)) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖finiteSynthesis (replicatedOrderedFamily f r) (elementaryPattern k z a)‖ ≤
      M * ‖finiteSynthesis (replicatedOrderedFamily f r) a‖ := by
  obtain ⟨⟨i, l⟩, rfl⟩ := copiedIndexEquiv.surjective k
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by linarith) (norm_nonneg _))).mp
  rw [mul_pow, replicatedOrderedFamily_synthesis_norm_sq,
    replicatedOrderedFamily_synthesis_norm_sq, copiedCoefficients_elementaryPattern]
  exact copiedEnergy_pattern_bound f hr hM hf hdef hbudget _ i l z hz

/-- Conditional replication gives a finite sign model without any loss of
witness gain. Equality transport from `n*r` to `r*n` keeps each numerical index
fixed, as in `replicationDimensionEquiv`. -/
theorem hasFiniteSignModel_of_replication (f : Fin n → H) {r : ℕ} (hr : 0 < r)
    {M c C g : ℝ} (hM : 1 ≤ M) (hf : ∀ i, ‖f i‖ = 1)
    (hdef : HasReplicationDeficits f M c C) (hbudget : C ≤ ((r : ℝ) - 1) * c)
    (p : Fin n → Bool) (a : Fin n → ℂ) (ha : a ≠ 0)
    (hgain : g ^ 2 * ‖finiteSynthesis f a‖ ^ 2 ≤
      ‖finiteSynthesis f ((fun i => if p i then (-1 : ℂ) else 1) * a)‖ ^ 2) :
    HasFiniteSignModel.{u} M (r * n) g := by
  rw [Nat.mul_comm r n]
  let pf : Fin (n * r) → Bool := fun k => p (copiedIndexEquiv.symm k).1
  let pn : ℕ → Bool := fun k => if hk : k < n * r then pf ⟨k, hk⟩ else false
  have hpn (k : Fin (n * r)) : pn k.val = pf k := by simp [pn, k.isLt]
  refine ⟨ReplicatedSpace H n r, inferInstance, inferInstance,
    replicatedOrderedFamily f r, replicatedOrderedFamily_norm f hr hf,
    replicatedOrderedFamily_pattern_bound f hr hM hf hdef hbudget,
    pn, copiedOrderedLift r a, copiedOrderedLift_ne_zero hr ha, ?_⟩
  have hsign : ((fun k : Fin (n * r) => if pn k.val then (-1 : ℂ) else 1) *
      copiedOrderedLift r a) =
      copiedOrderedLift r ((fun i => if p i then (-1 : ℂ) else 1) * a) := by
    apply copiedCoefficients.injective
    funext i l
    simp only [copiedCoefficients_apply, Pi.mul_apply, hpn, pf,
      Equiv.symm_apply_apply, copiedOrderedLift_apply]
    change (if p i then (-1 : ℂ) else 1) * copiedLift r a i l =
      copiedLift r ((fun j => if p j then (-1 : ℂ) else 1) * a) i l
    simp only [copiedLift, Pi.mul_apply]
    ring
  rw [hsign, replicatedOrderedFamily_copiedLift_norm f hr,
    replicatedOrderedFamily_copiedLift_norm f hr]
  exact hgain

/-- Positive endpoint surplus allows one fixed replication count. -/
theorem exists_hasFiniteSignModel_of_replication (f : Fin n → H)
    {M c C g : ℝ} (hM : 1 ≤ M) (hc : 0 < c) (hf : ∀ i, ‖f i‖ = 1)
    (hdef : HasReplicationDeficits f M c C)
    (p : Fin n → Bool) (a : Fin n → ℂ) (ha : a ≠ 0)
    (hgain : g ^ 2 * ‖finiteSynthesis f a‖ ^ 2 ≤
      ‖finiteSynthesis f ((fun i => if p i then (-1 : ℂ) else 1) * a)‖ ^ 2) :
    ∃ r : ℕ, 1 ≤ r ∧ HasFiniteSignModel.{u} M (r * n) g := by
  obtain ⟨r, hr, hbudget⟩ := exists_replication_count (C := C) hc
  exact ⟨r, hr, hasFiniteSignModel_of_replication f (by omega) hM hf hdef hbudget p a ha hgain⟩

/-- The source's alternating coefficient vector is an explicit nonzero gain
witness; repeating its signs converts it exactly to the all-ones vector. -/
theorem hasFiniteSignModel_of_alternating_replication (f : Fin n → H)
    (hn : 0 < n) {r : ℕ} (hr : 0 < r) {M c C g : ℝ} (hM : 1 ≤ M)
    (hf : ∀ i, ‖f i‖ = 1) (hdef : HasReplicationDeficits f M c C)
    (hbudget : C ≤ ((r : ℝ) - 1) * c)
    (hgain : g ^ 2 * ‖finiteSynthesis f (fun i => (-1 : ℂ) ^ i.val)‖ ^ 2 ≤
      ‖finiteSynthesis f (fun _ => 1)‖ ^ 2) :
    HasFiniteSignModel.{u} M (r * n) g := by
  let a : Fin n → ℂ := fun i => (-1 : ℂ) ^ i.val
  let p : Fin n → Bool := fun i => decide (¬Even i.val)
  have ha : a ≠ 0 := by
    intro h
    have hi := congrFun h ⟨0, hn⟩
    norm_num [a] at hi
  have hsign (i : Fin n) : (if p i then (-1 : ℂ) else 1) = (-1 : ℂ) ^ i.val := by
    by_cases hi : Even i.val <;> simp [p, hi, neg_one_pow_eq_ite]
  have hone : ((fun i => if p i then (-1 : ℂ) else 1) * a) = (fun _ => 1) := by
    funext i
    simp only [Pi.mul_apply, hsign, a]
    rcases neg_one_pow_eq_or ℂ i.val with hi | hi <;> simp [hi]
  apply hasFiniteSignModel_of_replication f hr hM hf hdef hbudget p a ha
  rw [hone]
  exact hgain

end ProofProject
