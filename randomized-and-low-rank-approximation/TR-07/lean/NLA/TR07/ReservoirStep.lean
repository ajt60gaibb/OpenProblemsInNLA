import NLA.TR07.FirstHit
import NLA.TR07.IdealKernel
import NLA.TR07.CoupledPaths

/-! A first-hit transition uses only columns in its retained reservoir chunk.
Its unconditional law dominates a fixed fraction of the regularized ideal law. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace NLA.TR07
open Law
variable {α : Type*} [Fintype α] {k s ℓ : ℕ}

def reservoirDraw (u : α → Vec k) (z : Fin ℓ → α) (i : Fin k) : Law (Option α) :=
  half (Law.pure none) (Law.pure (firstHit (fun a => u a i ≠ 0) z))

def reservoirDrawLaw (p : Law α) (u : α → Vec k) (ℓ : ℕ) (i : Fin k) : Law (Option α) :=
  half (Law.pure none) (firstHitLaw p (fun a => u a i ≠ 0) ℓ)

theorem reservoirDraw_expect (p : Law α) (u : α → Vec k) (i : Fin k) (f : Option α → ℝ) :
    (p.iid ℓ).expect (fun z => (reservoirDraw u z i).expect f) =
      (reservoirDrawLaw p u ℓ i).expect f := by
  simp only [reservoirDraw, reservoirDrawLaw, expect_half, expect_pure,
    firstHitLaw, expect_map]
  simp only [div_eq_mul_inv, expect_mul_const, expect_add, expect_const]

theorem incidence_eq_prob (p : Law α) (u : α → Vec k)
    (hu : ∀ a, SignedVector s (u a)) (i : Fin k) :
    incidence p u i = p.prob (fun a => u a i ≠ 0) := by
  unfold incidence prob
  apply p.expect_congr
  intro a
  rw [(hu a).sq_eq]
  split_ifs <;> rfl

theorem reservoirDraw_dominates (p : Law α) (u : α → Vec k)
    (hu : ∀ a, SignedVector s (u a)) (hk : 0 < k) (hℓk : ℓ ≤ k)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1/2) (hck : c ≤ (ℓ : ℝ) / (2*k))
    (i : Fin k) (x : Option α) :
    c * (coordinateDraw p u hk i).wt x ≤ (reservoirDrawLaw p u ℓ i).wt x := by
  have hd := regDiagonal_pos p u hk i
  have hp0 := incidence_nonneg p u i
  have hp1 := incidence_le_one p u hu i
  have he := incidence_eq_prob p u hu i
  cases x with
  | none =>
    have hnon := (firstHitLaw p (fun a => u a i ≠ 0) ℓ).nonneg none
    change c * (1 - incidence p u i / regDiagonal p u i) ≤
      ((Law.pure (none : Option α)).wt none + (firstHitLaw p _ ℓ).wt none) / 2
    have hfrac : 0 ≤ incidence p u i / regDiagonal p u i := div_nonneg hp0 hd.le
    simp only [Law.pure, ↓reduceIte]
    nlinarith
  | some a =>
    change c * (p.wt a * (u a i)^2 / regDiagonal p u i) ≤
      ((Law.pure (none : Option α)).wt (some a) + (firstHitLaw p _ ℓ).wt (some a)) / 2
    rw [firstHitLaw_some, ← he, (hu a).sq_eq]
    simp only [Law.pure, reduceCtorEq, ↓reduceIte, zero_add]
    by_cases ha : u a i = 0
    · simp [ha]
    · rw [if_pos ha, if_pos ha, mul_one]
      have hg := geom_regularized_bound hp0 hp1 hk hℓk
      have hcr : 2*c ≤ (ℓ : ℝ)/k := by
        calc
          2*c ≤ 2*((ℓ : ℝ)/(2*k)) := by linarith
          _ = _ := by ring
      have hgd : c * 2 ≤ (∑ t ∈ Finset.range ℓ, (1 - incidence p u i)^t) *
          regDiagonal p u i := by simpa [regDiagonal, mul_comm] using hcr.trans hg
      have hdg : c / regDiagonal p u i ≤ (∑ t ∈ Finset.range ℓ, (1 - incidence p u i)^t) / 2 := by
        apply (div_le_iff₀ hd).mpr
        linarith
      calc
        _ = (c / regDiagonal p u i) * p.wt a := by ring
        _ ≤ ((∑ t ∈ Finset.range ℓ, (1 - incidence p u i)^t) / 2) * p.wt a :=
          mul_le_mul_of_nonneg_right hdg (p.nonneg a)
        _ = _ := by ring

def reservoirStep (u : α → Vec k) (hu : ∀ a, SignedVector s (u a)) (hs : 0 < s)
    : SignedState α → (Fin ℓ → α) → Law (SignedState α)
  | none, _ => Law.pure none
  | some (b,a), z =>
    (coordinateChoice (stateVector u (some (b,a))) (stateVector_signed u hu b a) hs).bind
      (fun i => (reservoirDraw u z i).map (orientDraw u i (stateVector u (some (b,a)) i)))

def reservoirKernel (p : Law α) (u : α → Vec k) (hu : ∀ a, SignedVector s (u a))
    (hs : 0 < s) (ℓ : ℕ) (x : SignedState α) : Law (SignedState α) :=
  (p.iid ℓ).bind (reservoirStep u hu hs x)

theorem reservoirKernel_dominates (p : Law α) (u : α → Vec k)
    (hu : ∀ a, SignedVector s (u a)) (hk : 0 < k) (hs : 0 < s) (hℓk : ℓ ≤ k)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1/2) (hck : c ≤ (ℓ : ℝ)/(2*k))
    (x y : SignedState α) :
    c * (idealKernel p u hu hk hs x).wt y ≤ (reservoirKernel p u hu hs ℓ x).wt y := by
  rw [wt_eq_expect (idealKernel _ _ _ _ _ _), wt_eq_expect (reservoirKernel _ _ _ _ _ _)]
  let f := fun z : SignedState α => @ite ℝ (z = y) (Classical.propDecidable _) 1 0
  change c * (idealKernel p u hu hk hs x).expect f ≤ (reservoirKernel p u hu hs ℓ x).expect f
  rcases x with _ | ⟨b,a⟩
  · simp only [idealKernel, reservoirKernel, reservoirStep, expect_bind, expect_pure, expect_const]
    have hf : 0 ≤ f none := by dsimp [f]; split_ifs <;> norm_num
    nlinarith
  · simp only [idealKernel, reservoirKernel, reservoirStep, expect_bind]
    rw [expect_comm]
    rw [← expect_const_mul]
    apply expect_mono
    intro i
    simp only [coordinateBranch, expect_map]
    rw [reservoirDraw_expect]
    exact scaled_expect_le _ _ (reservoirDraw_dominates p u hu hk hℓk hc0 hc1 hck i) _
      (fun z => by dsimp [f]; split_ifs <;> norm_num)

theorem reservoirStep_span (u : α → Vec k) (hu : ∀ a, SignedVector s (u a)) (hs : 0 < s)
    (x : SignedState α) (z : Fin ℓ → α) (y : SignedState α)
    (hy : 0 < (reservoirStep u hu hs x z).wt y) :
    stateVector u y ∈ Submodule.span ℝ (Set.range (fun i => u (z i))) := by
  rcases x with _ | ⟨b,a⟩
  · have he : y = none := by
      by_contra he
      simp [reservoirStep, Law.pure, he] at hy
    subst y
    exact Submodule.zero_mem _
  · obtain ⟨i, _, hi⟩ := bind_pos_witness _ _ y hy
    obtain ⟨w, hw, he⟩ := map_pos_witness _ _ y hi
    subst y
    rcases w with _ | a'
    · exact Submodule.zero_mem _
    · have hh : firstHit (fun a => u a i ≠ 0) z = some a' := by
        by_contra hh
        simp [reservoirDraw, half, Law.pure, Ne.symm hh] at hw
      obtain ⟨_, j, hj⟩ := firstHit_mem _ z hh
      have hm : u a' ∈ Submodule.span ℝ (Set.range (fun i => u (z i))) :=
        Submodule.subset_span ⟨j, congrArg u hj⟩
      exact Submodule.smul_mem _ _ hm

end NLA.TR07
