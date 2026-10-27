import NLA.Proofs.RE06.GaussianMomentRow

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace NLA.Proofs.RE06.GaussianMoment

def firstRowEquiv (d : ℕ) : Unit ⊕ Fin d ≃ Fin (d + 1) where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun := Fin.cases (Sum.inl ()) Sum.inr
  left_inv := by rintro (⟨⟩ | i) <;> rfl
  right_inv := by intro i; exact Fin.cases rfl (fun j => rfl) i

def finRowStack {d p : ℕ} (z : Fin p → ℝ) (W : Matrix (Fin d) (Fin p) ℝ) :
    Matrix (Fin (d + 1)) (Fin p) ℝ := Fin.cons z W

theorem finRowStack_submatrix {d p : ℕ} (z : Fin p → ℝ)
    (W : Matrix (Fin d) (Fin p) ℝ) :
    finRowStack z W = (rowStack z W).submatrix (firstRowEquiv d).symm id := by
  ext i j
  refine Fin.cases ?_ (fun k => ?_) i <;> rfl

theorem finRowStack_gram_submatrix {d p : ℕ} (z : Fin p → ℝ)
    (W : Matrix (Fin d) (Fin p) ℝ) :
    finRowStack z W * (finRowStack z W).transpose =
      (rowStack z W * (rowStack z W).transpose).submatrix
        (firstRowEquiv d).symm (firstRowEquiv d).symm := by
  rw [finRowStack_submatrix]
  simp only [Matrix.transpose_submatrix]
  exact (Matrix.submatrix_mul_equiv _ _ (Equiv.refl (Fin p))).symm

theorem fin_inverse_gram_first_entry {d p : ℕ} (z : Fin p → ℝ)
    (W : Matrix (Fin d) (Fin p) ℝ) :
    (finRowStack z W * (finRowStack z W).transpose)⁻¹ 0 0 =
      (rowStack z W * (rowStack z W).transpose)⁻¹ (Sum.inl ()) (Sum.inl ()) := by
  rw [finRowStack_gram_submatrix, Matrix.inv_submatrix_equiv]
  rfl

def rowEntryEquiv (d p : ℕ) : ((Fin d × Fin p) ⊕ Fin p) ≃ (Fin (d + 1) × Fin p) where
  toFun := Sum.elim (fun ij => (ij.1.succ, ij.2)) (fun j => (0, j))
  invFun := fun ij => Fin.cases (Sum.inr ij.2) (fun i => Sum.inl (i, ij.2)) ij.1
  left_inv := by rintro (⟨i,j⟩ | j) <;> rfl
  right_inv := by rintro ⟨i,j⟩; exact Fin.cases rfl (fun k => rfl) i

def joinedEntries {d p : ℕ} (x : ((Fin d × Fin p) → ℝ) × (Fin p → ℝ)) :
    (Fin (d + 1) × Fin p) → ℝ := fun ij => Fin.cons x.2 (entryMatrix x.1) ij.1 ij.2

theorem joinedEntries_hasLaw (d p : ℕ) :
    HasLaw (joinedEntries (d := d) (p := p))
      (Measure.pi (fun _ : Fin (d + 1) × Fin p => gaussianReal 0 1))
      ((Measure.pi (fun _ : Fin d × Fin p => gaussianReal 0 1)).prod
        (Measure.pi (fun _ : Fin p => gaussianReal 0 1))) := by
  let e := rowEntryEquiv d p
  have hsum := (measurePreserving_sumPiEquivProdPi_symm
    (fun _ : (Fin d × Fin p) ⊕ Fin p => gaussianReal 0 1)).hasLaw
  have hidx := (measurePreserving_piCongrLeft
    (fun _ : (Fin d × Fin p) ⊕ Fin p => gaussianReal 0 1) e).hasLaw
  have hh := hidx.comp hsum
  convert hh using 1
  funext x ij
  obtain ⟨i,j⟩ := ij
  refine Fin.cases ?_ (fun k => ?_) i <;> rfl

end NLA.Proofs.RE06.GaussianMoment
