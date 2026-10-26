import NLA.Proofs.TR04.TensorCompressionOriginal

/-! Explicit mixed-radix enumeration. No noncomputable finite enumeration is
used by this index map; zero modes and the empty mode product are included. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Matrix

namespace NLA.Proofs.TR04.TensorFormat

/-- Last-index-fastest enumeration by the actual finite product bijection. -/
def radixIndexEquiv : (ns : List ℕ) → Fin ns.prod ≃ Index ns
  | [] =>
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => ⟨0, by decide⟩
      left_inv := fun i => by
        apply Fin.ext
        have hi := i.isLt
        change 0 = i.val
        simp only [List.prod_nil] at hi
        omega
      right_inv := fun _ => Subsingleton.elim _ _ }
  | m :: ns =>
    finProdFinEquiv.symm.trans
      (Equiv.prodCongr (Equiv.refl (Fin m)) (radixIndexEquiv ns))

def radixOffset : (ns : List ℕ) → Index ns → ℕ
  | [], _ => 0
  | _ :: ns, x => x.1.val * ns.prod + radixOffset ns x.2

@[simp] theorem radixIndexEquiv_symm_val (ns : List ℕ) (x : Index ns) :
    ((radixIndexEquiv ns).symm x).val = radixOffset ns x := by
  induction ns with
  | nil => cases x; rfl
  | cons m ns ih =>
    change ((radixIndexEquiv ns).symm x.2).val + ns.prod * x.1.val =
      x.1.val * ns.prod + radixOffset ns x.2
    rw [ih]
    ac_rfl

theorem radixOffset_lt (ns : List ℕ) (x : Index ns) : radixOffset ns x < ns.prod := by
  rw [← radixIndexEquiv_symm_val]
  exact ((radixIndexEquiv ns).symm x).isLt

@[simp] theorem radixIndexEquiv_decode_encode (ns : List ℕ) (x : Index ns) :
    radixIndexEquiv ns ⟨radixOffset ns x, radixOffset_lt ns x⟩ = x := by
  have he : (⟨radixOffset ns x, radixOffset_lt ns x⟩ : Fin ns.prod) =
      (radixIndexEquiv ns).symm x := Fin.ext (radixIndexEquiv_symm_val ns x).symm
  rw [he, Equiv.apply_symm_apply]

/-- Cardinality normalization changes only a proof, not the numeric address. -/
def cardToProdEquiv (ns : List ℕ) : Fin (suffixSize ns) ≃ Fin ns.prod where
  toFun i := ⟨i.val, by rw [← card_index ns]; exact i.isLt⟩
  invFun i := ⟨i.val, by change i.val < Fintype.card (Index ns); rw [card_index ns]; exact i.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

def radixSuffixEquiv (ns : List ℕ) : Fin (suffixSize ns) ≃ Index ns :=
  (cardToProdEquiv ns).trans (radixIndexEquiv ns)

@[simp] theorem radixSuffixEquiv_symm_val (ns : List ℕ) (x : Index ns) :
    ((radixSuffixEquiv ns).symm x).val = radixOffset ns x :=
  radixIndexEquiv_symm_val ns x

theorem prod_modeList {d : ℕ} (n : Fin d → ℕ) : (modeList n).prod = ∏ i, n i := by
  induction d with
  | zero => simp [modeList]
  | succ d ih => simp only [modeList, List.prod_cons, Fin.prod_univ_succ, ih]

def vectorSuffixSize {d : ℕ} (n : Fin d → ℕ) (i : Fin d) : ℕ :=
  ∏ s ∈ Finset.univ.filter (fun s : Fin d => i < s), n s

@[simp] theorem vectorSuffixSize_zero {d : ℕ} (n : Fin (d + 1) → ℕ) :
    vectorSuffixSize n 0 = (modeList (fun i : Fin d => n i.succ)).prod := by
  simp [vectorSuffixSize, Finset.prod_filter, Fin.prod_univ_succ, prod_modeList]

@[simp] theorem vectorSuffixSize_succ {d : ℕ} (n : Fin (d + 1) → ℕ) (i : Fin d) :
    vectorSuffixSize n i.succ = vectorSuffixSize (fun i : Fin d => n i.succ) i := by
  simp [vectorSuffixSize, Finset.prod_filter, Fin.prod_univ_succ]

def vectorOffset {d : ℕ} (n : Fin d → ℕ) (x : (i : Fin d) → Fin (n i)) : ℕ :=
  ∑ i, (x i).val * vectorSuffixSize n i

/-- The explicit recursive address is exactly the original suffix-weight sum. -/
theorem radixOffset_vector {d : ℕ} (n : Fin d → ℕ) (x : (i : Fin d) → Fin (n i)) :
    radixOffset (modeList n) ((vectorIndexEquiv n).symm x) = vectorOffset n x := by
  induction d with
  | zero => simp [radixOffset, vectorOffset]
  | succ d ih =>
    change (x 0).val * (modeList (fun i : Fin d => n i.succ)).prod +
      radixOffset (modeList (fun i : Fin d => n i.succ))
        ((vectorIndexEquiv (fun i : Fin d => n i.succ)).symm (Fin.tail x)) = _
    rw [ih]
    simp only [vectorOffset, Fin.sum_univ_succ, vectorSuffixSize_zero,
      vectorSuffixSize_succ, Fin.tail]

theorem original_radixOffset (S : NLA.Computation.TensorTrainApproximation.Shape)
    (x : NLA.Computation.TensorTrainApproximation.Index S) :
    radixOffset (modeList S.mode) ((vectorIndexEquiv S.mode).symm x) =
      NLA.Computation.TensorTrainApproximation.Offset S x :=
  radixOffset_vector S.mode x

theorem original_offset_lt_denseSize (S : NLA.Computation.TensorTrainApproximation.Shape)
    (x : NLA.Computation.TensorTrainApproximation.Index S) :
    NLA.Computation.TensorTrainApproximation.Offset S x <
      NLA.Computation.TensorTrainApproximation.DenseSize S := by
  rw [← original_radixOffset]
  have h := radixOffset_lt (modeList S.mode) ((vectorIndexEquiv S.mode).symm x)
  simpa only [prod_modeList, NLA.Computation.TensorTrainApproximation.DenseSize] using h

#assert_trust kernel radixIndexEquiv
#assert_trust kernel radixIndexEquiv_symm_val
#assert_trust kernel radixIndexEquiv_decode_encode
#assert_trust kernel radixSuffixEquiv_symm_val
#assert_trust kernel radixOffset_vector
#assert_trust kernel original_radixOffset
#assert_trust kernel original_offset_lt_denseSize
#print axioms original_radixOffset
end NLA.Proofs.TR04.TensorFormat
