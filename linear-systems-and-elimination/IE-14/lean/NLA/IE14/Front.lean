/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, University of Cambridge.
The original-row front is derived from the literal complex GEPP trajectory.
-/
import NLA.IE14.Basic
import LeanCert.Tactic

noncomputable section
namespace NLA.IE14

/-- Original input label of a current physical row after the actual swaps. -/
def origin {n : ℕ} (path : PivotPath n) : ℕ → Equiv.Perm (Fin n)
  | 0 => Equiv.refl _
  | k+1 => if h : k<n then
      (Equiv.swap ⟨k,h⟩ (path ⟨k,h⟩)).trans (origin path k)
    else origin path k

theorem origin_step {n : ℕ} (path : PivotPath n) (k : ℕ) (hk : k<n) (i : Fin n) :
    origin path (k+1) i = origin path k (Equiv.swap ⟨k,hk⟩ (path ⟨k,hk⟩) i) := by
  simp only [origin, dif_pos hk, Equiv.trans_apply]

theorem origin_symm_step {n : ℕ} (path : PivotPath n) (k : ℕ) (hk : k<n) (a : Fin n) :
    (origin path (k+1)).symm a =
      Equiv.swap ⟨k,hk⟩ (path ⟨k,hk⟩) ((origin path k).symm a) := by
  simp only [origin, dif_pos hk, Equiv.symm_trans_apply, Equiv.symm_swap]

def remainingPair {n : ℕ} (r s f p : Fin n) : Fin n × Fin n :=
  if p=r then (s,f) else if p=s then (r,f) else (r,s)

theorem remainingPair_properties {n : ℕ} (r s f p : Fin n)
    (hrs : r ≠ s) (hrf : r ≠ f) (hsf : s ≠ f) (hp : p=r ∨ p=s ∨ p=f) :
    (remainingPair r s f p).1  ≠  (remainingPair r s f p).2 ∧
    ∀ q, (q=(remainingPair r s f p).1 ∨ q=(remainingPair r s f p).2) ↔
      (q=r ∨ q=s ∨ q=f) ∧ q ≠ p := by
  rcases hp with rfl | rfl | rfl
  · simp only [remainingPair]
    constructor
    · exact hsf
    · intro q; aesop
  · simp only [remainingPair, if_neg (Ne.symm hrs)]
    constructor
    · exact hrf
    · intro q; aesop
  · simp only [remainingPair, if_neg (Ne.symm hrf), if_neg (Ne.symm hsf)]
    constructor
    · exact hrs
    · intro q; aesop

/-- The two old physical rows, updated by deleting the actual chosen front row. -/
def frontPair {n : ℕ} (hn : 4 ≤ n) (path : PivotPath n) : ℕ → Fin n × Fin n
  | 0 => (⟨0,by omega⟩,⟨n-1,by omega⟩)
  | k+1 => if h : k+2<n then
      let z : Fin n := ⟨k,by omega⟩
      let f := (origin path k).symm ⟨k+1,by omega⟩
      let old := frontPair hn path k
      let rem := remainingPair old.1 old.2 f (path z)
      (Equiv.swap z (path z) rem.1, Equiv.swap z (path z) rem.2)
    else frontPair hn path k

theorem swap_survivor_active {n : ℕ} (k p q : Fin n) (hp : k ≤ p)
    (hq : k ≤ q) (hne : q ≠ p) : k<Equiv.swap k p q := by
  have hle := swap_active k p q hp hq
  apply lt_of_le_of_ne hle
  intro he
  have h := congrArg (Equiv.swap k p) he
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_self] at h
  exact hne h.symm

theorem trajectory_survivor_entry {n : ℕ} (A : Mat n) (path : PivotPath n)
    (k : ℕ) (hk : k<n) (q j : Fin n)
    (hp : k ≤ (path ⟨k,hk⟩).val) (hq : k ≤ q.val)
    (hne : q ≠ path ⟨k,hk⟩) (hj : k<j.val) :
    trajectory A path (k+1) (Equiv.swap ⟨k,hk⟩ (path ⟨k,hk⟩) q) j =
      trajectory A path k q j -
        (trajectory A path k q ⟨k,hk⟩ / trajectory A path k (path ⟨k,hk⟩) ⟨k,hk⟩) *
          trajectory A path k (path ⟨k,hk⟩) j := by
  have hi := swap_survivor_active ⟨k,hk⟩ (path ⟨k,hk⟩) q hp hq hne
  rw [trajectory, dif_pos hk]
  change (if (⟨k,hk⟩ : Fin n) < Equiv.swap ⟨k,hk⟩ (path ⟨k,hk⟩) q ∧
      (⟨k,hk⟩ : Fin n) < j then _ else _) = _
  rw [if_pos ⟨hi,hj⟩]
  unfold rowSwap
  simp only [Equiv.swap_apply_self, Equiv.swap_apply_left]

/-- Full original-label bookkeeping; future rows retain their actual input entries. -/
structure FrontInvariant {n : ℕ} (A : Mat n) (path : PivotPath n)
    (k : ℕ) (r s : Fin n) : Prop where
  left_active : k ≤ r.val
  right_active : k ≤ s.val
  distinct : r ≠ s
  left_label : (origin path k r).val ≤ k ∨ (origin path k r).val+1=n
  right_label : (origin path k s).val ≤ k ∨ (origin path k s).val+1=n
  cover : ∀ i : Fin n, k ≤ i.val → i ≠ r → i ≠ s →
    k < (origin path k i).val ∧ (origin path k i).val+1<n
  future_active : ∀ a : Fin n, k<a.val → a.val+1<n →
    k ≤ ((origin path k).symm a).val
  future_value : ∀ a : Fin n, k<a.val → a.val+1<n →
    ∀ j : Fin n, k ≤ j.val → trajectory A path k ((origin path k).symm a) j = A a j

theorem frontInvariant_initial {n : ℕ} (hn : 4 ≤ n) (A : Mat n) (path : PivotPath n) :
    FrontInvariant A path 0 (frontPair hn path 0).1 (frontPair hn path 0).2 := by
  constructor
  · simp [frontPair]
  · simp [frontPair]
  · simp only [frontPair, ne_eq, Fin.mk.injEq]
    omega
  · simp [origin, frontPair]
  · right; simp only [origin, frontPair, Equiv.refl_apply]; omega
  · intro i hi hl hr
    simp only [origin, Equiv.refl_apply]
    have hli : i.val ≠ 0 := by
      intro he; apply hl; apply Fin.ext; simpa [frontPair] using he
    have hri : i.val ≠ n-1 := by
      intro he; apply hr; apply Fin.ext; simpa [frontPair] using he
    omega
  · intro a ha hb; exact Nat.zero_le _
  · intro a ha hb j hj; rfl

theorem front_fresh_distinct {n : ℕ} {A : Mat n} {path : PivotPath n}
    {k : ℕ} {r s : Fin n} (hF : FrontInvariant A path k r s) (hk : k+2<n) :
    let f := (origin path k).symm (⟨k+1,by omega⟩ : Fin n)
    k ≤ f.val ∧ r ≠ f ∧ s ≠ f := by
  dsimp only
  refine ⟨hF.future_active _ (by simp) (by simp; omega), ?_, ?_⟩
  · intro he
    have hv := congrArg (fun i => (origin path k i).val) he
    simp only [Equiv.apply_symm_apply] at hv
    have hr := hF.left_label
    change (origin path k r).val=k+1 at hv
    omega
  · intro he
    have hv := congrArg (fun i => (origin path k i).val) he
    simp only [Equiv.apply_symm_apply] at hv
    have hs := hF.right_label
    change (origin path k s).val=k+1 at hv
    omega

theorem pivot_in_front {n : ℕ} {A : Mat n} {path : PivotPath n}
    {k : ℕ} {r s : Fin n} (hA : CyclicInput A) (hp : AdmissiblePath A path)
    (hF : FrontInvariant A path k r s) (hk : k+2<n) :
    path ⟨k,by omega⟩=r ∨ path ⟨k,by omega⟩=s ∨
      path ⟨k,by omega⟩=(origin path k).symm ⟨k+1,by omega⟩ := by
  let z : Fin n := ⟨k,by omega⟩
  let p := path z
  by_cases hr : p=r
  · exact Or.inl hr
  by_cases hs : p=s
  · exact Or.inr (Or.inl hs)
  right; right
  by_contra hf
  have hcover := hF.cover p (hp z).1 hr hs
  have hlabel : (origin path k p).val ≠ k+1 := by
    intro he
    apply hf
    apply (origin path k).injective
    simp only [Equiv.apply_symm_apply]
    exact Fin.ext he
  have hz : A (origin path k p) z=0 := by
    apply hA.2.1
    simp only [CyclicPosition]
    have hzval : z.val=k := rfl
    omega
  have he := hF.future_value (origin path k p) hcover.1 hcover.2 z le_rfl
  simp only [Equiv.symm_apply_apply] at he
  exact (hp z).2.1 (he.trans hz)

theorem frontInvariant_advance {n : ℕ} {A : Mat n} {path : PivotPath n}
    {k : ℕ} {r s : Fin n} (hA : CyclicInput A) (hp : AdmissiblePath A path)
    (hF : FrontInvariant A path k r s) (hk : k+2<n) :
    let z : Fin n := ⟨k,by omega⟩
    let f := (origin path k).symm (⟨k+1,by omega⟩ : Fin n)
    let rem := remainingPair r s f (path z)
    FrontInvariant A path (k+1)
      (Equiv.swap z (path z) rem.1) (Equiv.swap z (path z) rem.2) := by
  let z : Fin n := ⟨k,by omega⟩
  let f := (origin path k).symm (⟨k+1,by omega⟩ : Fin n)
  let p := path z
  let τ := Equiv.swap z p
  let rem := remainingPair r s f p
  change FrontInvariant A path (k+1) (τ rem.1) (τ rem.2)
  have hf := front_fresh_distinct hF hk
  change k ≤ f.val ∧ r ≠ f ∧ s ≠ f at hf
  have hpf := pivot_in_front hA hp hF hk
  change p=r ∨ p=s ∨ p=f at hpf
  have hrem := remainingPair_properties r s f p hF.distinct hf.2.1 hf.2.2 hpf
  change rem.1 ≠ rem.2 ∧ ∀ q, (q=rem.1 ∨ q=rem.2) ↔
    (q=r ∨ q=s ∨ q=f) ∧ q ≠ p at hrem
  have hmem₁ := (hrem.2 rem.1).mp (Or.inl rfl)
  have hmem₂ := (hrem.2 rem.2).mp (Or.inr rfl)
  have hactive : ∀ q : Fin n, q=r ∨ q=s ∨ q=f → k ≤ q.val := by
    intro q hq
    rcases hq with rfl | rfl | rfl
    · exact hF.left_active
    · exact hF.right_active
    · exact hf.1
  have hlabel : ∀ q : Fin n, q=r ∨ q=s ∨ q=f →
      (origin path k q).val ≤ k+1 ∨ (origin path k q).val+1=n := by
    intro q hq
    rcases hq with rfl | rfl | rfl
    · have h := hF.left_label; omega
    · have h := hF.right_label; omega
    · left; simp [f]
  have hplabel := hlabel p hpf
  have hfuture : ∀ a : Fin n, k+1<a.val → a.val+1<n →
      k ≤ ((origin path k).symm a).val ∧ (origin path k).symm a ≠ p := by
    intro a ha hb
    refine ⟨hF.future_active a (by omega) hb, ?_⟩
    intro he
    have hv := congrArg (fun q => (origin path k q).val) he
    simp only [Equiv.apply_symm_apply] at hv
    omega
  have ho : ∀ i : Fin n, origin path (k+1) i = origin path k (τ i) := by
    intro i; exact origin_step path k z.isLt i
  constructor
  · exact swap_survivor_active z p rem.1 (hp z).1 (hactive _ hmem₁.1) hmem₁.2
  · exact swap_survivor_active z p rem.2 (hp z).1 (hactive _ hmem₂.1) hmem₂.2
  · exact fun he => hrem.1 (τ.injective he)
  · rw [ho]; simp only [τ, Equiv.swap_apply_self]; exact hlabel _ hmem₁.1
  · rw [ho]; simp only [τ, Equiv.swap_apply_self]; exact hlabel _ hmem₂.1
  · intro i hi hir his
    let q := τ i
    have hki : z ≤ i := by change k ≤ i.val; omega
    have hq : k ≤ q.val := swap_active z p i (hp z).1 hki
    have hqp : q ≠ p := by
      intro he
      have he' := congrArg τ he
      simp only [q, τ, Equiv.swap_apply_self, Equiv.swap_apply_right] at he'
      have hv := congrArg Fin.val he'
      change i.val=k at hv
      omega
    have hqrem₁ : q ≠ rem.1 := by
      intro he; apply hir
      have he' := congrArg τ he
      simpa only [q, τ, Equiv.swap_apply_self] using he'
    have hqrem₂ : q ≠ rem.2 := by
      intro he; apply his
      have he' := congrArg τ he
      simpa only [q, τ, Equiv.swap_apply_self] using he'
    have hqfront : ¬(q=r ∨ q=s ∨ q=f) := by
      intro he
      rcases (hrem.2 q).mpr ⟨he,hqp⟩ with h | h
      · exact hqrem₁ h
      · exact hqrem₂ h
    have hr : q ≠ r := fun he => hqfront (Or.inl he)
    have hs : q ≠ s := fun he => hqfront (Or.inr (Or.inl he))
    have hqf : q ≠ f := fun he => hqfront (Or.inr (Or.inr he))
    have hc := hF.cover q hq hr hs
    have hv : (origin path k q).val ≠ k+1 := by
      intro he; apply hqf
      apply (origin path k).injective
      simp only [f, Equiv.apply_symm_apply]
      exact Fin.ext he
    rw [ho]
    change k+1<(origin path k q).val ∧ (origin path k q).val+1<n
    omega
  · intro a ha hb
    rw [origin_symm_step path k z.isLt a]
    exact swap_survivor_active z p _ (hp z).1 (hfuture a ha hb).1 (hfuture a ha hb).2
  · intro a ha hb j hj
    rw [origin_symm_step path k z.isLt a]
    rw [trajectory_survivor_entry A path k z.isLt _ j (hp z).1
      (hfuture a ha hb).1 (hfuture a ha hb).2 hj]
    rw [hF.future_value a (by omega) hb j (by omega)]
    rw [hF.future_value a (by omega) hb z le_rfl]
    have hz : A a z=0 := by
      apply hA.2.1
      simp only [CyclicPosition]
      have hzval : z.val=k := rfl
      omega
    simp [hz]

theorem frontInvariant_all {n : ℕ} (hn : 4 ≤ n) (A : Mat n) (hA : CyclicInput A)
    (path : PivotPath n) (hp : AdmissiblePath A path) (k : ℕ) (hk : k ≤ n-2) :
    FrontInvariant A path k (frontPair hn path k).1 (frontPair hn path k).2 := by
  induction k with
  | zero => exact frontInvariant_initial hn A path
  | succ k ih =>
    have hk' : k+2<n := by omega
    have h := frontInvariant_advance hA hp (ih (by omega)) hk'
    simpa only [frontPair, dif_pos hk'] using h

#assert_trust kernel frontInvariant_all
#print axioms frontInvariant_all

end NLA.IE14
