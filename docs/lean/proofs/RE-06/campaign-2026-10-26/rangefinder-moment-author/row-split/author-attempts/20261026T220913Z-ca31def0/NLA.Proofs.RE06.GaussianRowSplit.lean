import NLA.Proofs.RE06.GaussianStream

/-! The first-r and remaining Gaussian rows have their actual independent
finite product laws, including empty head or tail blocks. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Matrix
namespace NLA.Proofs.RE06

def gaussianTailRow (n r : ℕ) (hr : r ≤ n) (i : Fin (n-r)) : Fin n :=
  ⟨r + i.val, by omega⟩

def gaussianRowIndexEquiv (n r k : ℕ) (hr : r ≤ n) :
    (Fin r × Fin k) ⊕ (Fin (n-r) × Fin k) ≃ Fin n × Fin k where
  toFun := Sum.elim (fun p => (Fin.castLE hr p.1, p.2))
    (fun p => (gaussianTailRow n r hr p.1, p.2))
  invFun := fun p => if h : p.1.val < r then
    Sum.inl (⟨p.1.val, h⟩, p.2) else
    Sum.inr (⟨p.1.val-r, by omega⟩, p.2)
  left_inv := by
    intro p
    rcases p with p | p
    · simp only [Sum.elim_inl, Fin.val_castLE, p.1.isLt, ↓reduceDIte]
    · dsimp only
      split_ifs with h
      · have hh : r + p.1.val < r := h
        omega
      · congr 2
        apply Fin.ext
        change r + p.1.val - r = p.1.val
        omega
  right_inv := by
    intro p
    dsimp
    split_ifs with h
    · apply Prod.ext
      · apply Fin.ext
        rfl
      · rfl
    · apply Prod.ext
      · apply Fin.ext
        dsimp [gaussianTailRow]
        omega
      · rfl

def gaussianHeadEntries (n r k : ℕ) (hr : r ≤ n) (x : Fin n × Fin k → ℝ) :
    Fin r × Fin k → ℝ := fun p => x (Fin.castLE hr p.1, p.2)

def gaussianTailEntries (n r k : ℕ) (hr : r ≤ n) (x : Fin n × Fin k → ℝ) :
    Fin (n-r) × Fin k → ℝ := fun p => x (gaussianTailRow n r hr p.1, p.2)

/-- The exact joint head/tail finite product law. -/
theorem gaussian_row_split_hasLaw (n r k : ℕ) (hr : r ≤ n) :
    HasLaw (fun x : Fin n × Fin k → ℝ =>
      (gaussianHeadEntries n r k hr x, gaussianTailEntries n r k hr x))
      ((Measure.pi (fun _ : Fin r × Fin k => gaussianReal 0 1)).prod
       (Measure.pi (fun _ : Fin (n-r) × Fin k => gaussianReal 0 1)))
      (Measure.pi (fun _ : Fin n × Fin k => gaussianReal 0 1)) := by
  let e := gaussianRowIndexEquiv n r k hr
  have he := (measurePreserving_piCongrLeft
    (fun _ : Fin n × Fin k => gaussianReal 0 1) e).symm
  have hs := measurePreserving_sumPiEquivProdPi
    (fun _ : (Fin r × Fin k) ⊕ (Fin (n-r) × Fin k) => gaussianReal 0 1)
  convert (hs.comp he).hasLaw using 1
  funext x
  apply Prod.ext
  · funext p
    rfl
  · funext p
    rfl

/-- Transport of the split along any genuine full-entry Gaussian law. -/
theorem hasLaw_gaussian_row_split {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (n r k : ℕ) (hr : r ≤ n) (X : Ω → Fin n × Fin k → ℝ)
    (hX : HasLaw X (Measure.pi (fun _ : Fin n × Fin k => gaussianReal 0 1)) μ) :
    HasLaw (fun ω =>
      (gaussianHeadEntries n r k hr (X ω), gaussianTailEntries n r k hr (X ω)))
      ((Measure.pi (fun _ : Fin r × Fin k => gaussianReal 0 1)).prod
       (Measure.pi (fun _ : Fin (n-r) × Fin k => gaussianReal 0 1))) μ :=
  (gaussian_row_split_hasLaw n r k hr).fun_comp hX

#assert_trust kernel gaussianTailRow
#assert_trust kernel gaussianRowIndexEquiv
#assert_trust kernel gaussian_row_split_hasLaw
#assert_trust kernel hasLaw_gaussian_row_split
#print axioms gaussianTailRow
#print axioms gaussianRowIndexEquiv
#print axioms gaussian_row_split_hasLaw
#print axioms hasLaw_gaussian_row_split
end NLA.Proofs.RE06
